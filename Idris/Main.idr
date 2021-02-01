module Main

import Control.ST

data Term : Type where
  Var : String -> Term
  Lam : String -> Term -> Term
  App : Term -> Term -> Term
  Num : Int -> Term
  Add : Term -> Term -> Term

Show Term where
  show (Var x) = x
  show (Lam x y) = "λ" ++ x ++ "." ++ show y
  show (App x y) = "(" ++ show x ++ " " ++ show y ++ ")"
  show (Num x) = show x
  show (Add x y) = "(" ++ show x ++ "+" ++ show y ++ ")"

data TType : Type where
  TypeVar : String -> TType
  ArrowType : TType -> TType -> TType
  NumType : TType

Eq TType where
  (TypeVar s) == (TypeVar t) = s == t
  NumType == NumType = True
  (ArrowType s1 s2) == (ArrowType t1 t2) = s1 == t1 && s2 == t2
  _ == _ = False

Show TType where
  show (TypeVar x) = x
  show (ArrowType x y) = "(" ++ show x ++ " → " ++ show y ++ ")"
  show NumType = "ℕ"

Cast TType Type where
  cast NumType = Int
  cast (ArrowType t1 t2) = cast t1 -> cast t2
  cast (TypeVar var) = Type

infixr 20 <=>
data Equality = (<=>) TType TType

data Error : Type where
  UnboundVariable : String -> Error
  OccursIn : TType -> TType -> Error

Show Error where
  show (UnboundVariable var) = var ++ " is an unbound variable."
  show (OccursIn t1 t2) = show t1 ++ " occurs in " ++ show t2

startingVar : TType
startingVar = TypeVar "α₁"

constraints :
  Term -> TType -> (assignment, stream : Var)
  -> ST (Either Error) (List Equality) [assignment ::: State (List (String,String)),
                                        stream ::: State (Stream Char)]
constraints (Var var) t assignment _ = do
  ctx <- read assignment
  case lookup var ctx of
    Just var' => pure [t <=> (TypeVar var')]
    Nothing => lift $ Left $ UnboundVariable var
constraints (Lam x z) t assignment stream = do
  ctx <- read assignment
  s <- read stream
  let [a,b] = map singleton $ take 2 s
  write stream (drop 2 s)
  write assignment ((x,a)::ctx)
  e <- constraints z (TypeVar b) assignment stream
  pure $ [t <=> (ArrowType (TypeVar a) (TypeVar b))] ++ e
constraints (App t1 t2) t assignment stream = do
  ctx <- read assignment
  s <- read stream
  let a = singleton $ head s
  write stream (tail s)
  t1 <- constraints t1 (ArrowType (TypeVar a) t) assignment stream
  write assignment ctx
  t2 <- constraints t2 (TypeVar a) assignment stream
  pure $ t1 ++ t2
constraints (Num x) t _ _ = pure [t <=> NumType]
constraints (Add t1 t2) t assignment stream = do
  ctx <- read assignment
  t1 <- constraints t1 NumType assignment stream
  write assignment ctx
  t2 <- constraints t2 NumType assignment stream
  pure $ [t <=> NumType] ++ t1 ++ t2

getConstraints : Term -> Either Error (List Equality)
getConstraints term = run $ do
  stream <- new $ enumFrom 'α'
  assignment <- new []
  eqs <- constraints term startingVar assignment stream
  delete assignment
  delete stream
  pure eqs

-- | Is Type a (Sub-)Type of another Type
occursIn : TType -> TType -> Bool
occursIn t (ArrowType t1 t2) = (t `occursIn` t1) || (t `occursIn` t2)
occursIn t s = t == s

inAny : TType -> (List Equality) -> Bool
inAny t = foldr (\(t1 <=> t2), y => (t `occursIn` t1) || (t `occursIn` t2) || y) False


-- | Replace t for s in Equality
substitute : TType -> TType -> Equality -> Equality
substitute t s (t1 <=> t2) = subst t s t1 <=> subst t s t2
     where subst t s (ArrowType t1 t2) = ArrowType (subst t s t1) (subst t s t2)
           subst t s NumType = NumType
           subst t s x = if s == x then t else x

-- | Robinsons Unification algorithm
unify : (List Equality) -> Either Error (List Equality)
unify (((ArrowType t1 t2) <=> (ArrowType s1 s2))::eqs) = unify $ [t1 <=> s1, t2 <=> s2] ++ eqs
unify ((t@(TypeVar _) <=> s@(TypeVar _))::eqs) = if t == s
                                                 then unify eqs
                                                 else if t `inAny` eqs
                                                      then ((t <=> s)::) <$> unify (map (substitute s t) eqs)
                                                      else ((t <=> s)::) <$> unify eqs
unify ((t <=> s@(TypeVar _))::eqs) = unify ((s <=> t)::eqs)
unify ((t <=> NumType)::eqs) = ((t <=> NumType)::) <$> unify (map (substitute NumType t) eqs)
unify ((t <=> s)::eqs) = if t `occursIn` s
                         then Left $ OccursIn t s
                         else if t `inAny` eqs
                              then ((t <=> s)::) <$> unify (map (substitute s t) eqs)
                              else ((t <=> s)::) <$> unify eqs
unify [] = pure []

partial
getStart : List Equality -> TType
getStart ((t <=> s)::eqs) = if t == startingVar then s
                            else if s == startingVar then t
                            else getStart eqs

-- | Bonus: Evaluation
eval : Term -> Term
eval (Add t1 t2) = case (eval t1, eval t2) of
    (Num a, Num b) => Num $ a+b
    (a,b) => Add a b
eval (App (Lam v t1) t2) = eval $ subst (eval t2) v t1
  where subst t s (Var s') = if s == s' then t else Var s'
        subst t s (Lam v t') = if s == v then Lam v t' else Lam v $ subst t s t'
        subst t s (App t1 t2) = App (subst t s t1) (subst t s t2)
        subst t s (Add t1 t2) = Add (subst t s t1) (subst t s t2)
        subst t s (Num n) = Num n
eval (App t1 t2) = App (eval t1) (eval t2)
eval (Lam v t) = Lam v $ eval t
eval lit = lit

typeCheck : Term -> String
typeCheck term = case getConstraints term of
     Left err =>  "Error while collecting constraints: " ++ show err
     Right eqs => case unify (reverse eqs) of
       Left err => "Error while unifying constraints: " ++ show err
       Right eqs' => show term ++ " : "  ++ show (getStart eqs')


-- | Exmaple terms
term1 : Term
term1 = Lam "x" $ Var "x"
term2 : Term
term2 = App term1 $ Num 42
term3 : Term
term3 = Lam "y" term2
term4 : Term
term4 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
plus1 : Term
plus1 = Lam "x" (Add (Var "x") (Num 1))
times2 : Term
times2 = Lam "x" (Add (Var "x") (Var "x"))
arith : Term
arith = Lam "f" (Lam "x" (Add (App (Var "f") (Var "x")) (Var "x")))
omega : Term
omega = Lam "x" (App (Var "x") (Var "x"))


main : IO ()
main = do
  putStrLn $ typeCheck term1
  putStrLn $ typeCheck term2
  putStrLn $ typeCheck term3
  putStrLn $ typeCheck term4
  putStrLn $ typeCheck plus1
  putStrLn $ typeCheck times2
  putStrLn $ typeCheck arith
  putStrLn $ typeCheck omega
