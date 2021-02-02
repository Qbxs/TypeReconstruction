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
  NumClash : TType -> Error

Show Error where
  show (UnboundVariable var) = var ++ " is an unbound variable."
  show (OccursIn t1 t2) = show t1 ++ " occurs in " ++ show t2
  show (NumClash t) = "Can not unify " ++ show NumType ++ " with " ++ show t

startingVar : TType
startingVar = TypeVar "α₁"

constraints :
  Term -> TType -> (context, stream : Var)
  -> ST (Either Error) (List Equality) [context ::: State (List (String,String)),
                                        stream ::: State (Stream Char)]
constraints (Var var) t context _ = do
  ctx <- read context
  case lookup var ctx of
    Just var' => pure [t <=> (TypeVar var')]
    Nothing => lift $ Left $ UnboundVariable var
constraints (Lam x z) t context stream = do
  let [a,b] = map singleton $ take 2 !(read stream)
  update stream (drop 2)
  update context ((x,a)::)
  e <- constraints z (TypeVar b) context stream
  pure $ [t <=> (ArrowType (TypeVar a) (TypeVar b))] ++ e
constraints (App t1 t2) t context stream = do
  ctx <- read context
  let a = singleton $ head !(read stream)
  update stream tail
  t1 <- constraints t1 (ArrowType (TypeVar a) t) context stream
  write context ctx
  t2 <- constraints t2 (TypeVar a) context stream
  pure $ t1 ++ t2
constraints (Num x) t _ _ = pure [t <=> NumType]
constraints (Add t1 t2) t context stream = do
  ctx <- read context
  t1 <- constraints t1 NumType context stream
  write context ctx
  t2 <- constraints t2 NumType context stream
  pure $ [t <=> NumType] ++ t1 ++ t2


getConstraints : Term -> Either Error (List Equality)
getConstraints term = run $ do
  stream <- new $ enumFrom 'α'
  context <- new []
  eqs <- constraints term startingVar context stream
  delete context
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
unify ((t@(TypeVar _) <=> s@(TypeVar _))::eqs) = if t == s then unify eqs
                                                 else ((t <=> s)::) <$> if t `inAny` eqs
                                                                        then unify (map (substitute s t) eqs)
                                                                        else unify eqs
unify ((t <=> s@(TypeVar _))::eqs) = unify ((s <=> t)::eqs)
unify ((NumType <=> NumType)::eqs) = unify eqs
unify ((NumType <=> t)::eqs) = unify (t <=> NumType::eqs)
unify ((t@(ArrowType _ _) <=> NumType)::eqs) = Left $ NumClash t
unify ((t <=> NumType)::eqs) = ((t <=> NumType)::) <$> if t `inAny` eqs
                                                       then unify (map (substitute NumType t) eqs)
                                                       else unify eqs
unify ((t <=> s)::eqs) = if t `occursIn` s then Left $ OccursIn t s
                         else ((t <=> s)::) <$> if t `inAny` eqs
                                                then unify (map (substitute s t) eqs)
                                                else unify eqs
unify [] = pure []

partial
getStart : List Equality -> TType
getStart ((t <=> s)::eqs) = if t == startingVar then s
                            else if s == startingVar then t
                            else getStart eqs

-- | Bonus: Evaluation
eval : Term -> Term
eval (Add t1 t2) = case (eval t1, eval t2) of
    (Num 0, b) => b
    (a, Num 0) => a
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
       Right eqs' => show term ++ " ▷ " ++ show (eval term) ++ " : "  ++ show (getStart eqs')


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
plus1 = Lam "x" (Add (Num 0) (Var "x"))
times2 : Term
times2 = Lam "x" (Add (Var "x") (Var "x"))
arith : Term
arith = Lam "f" (Lam "x" (Add (App (Var "f") (Var "x")) (Var "x")))
sCombinator : Term
sCombinator = Lam "x" (Lam "y" (Lam "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))
kCombinator : Term
kCombinator = Lam "t" (Lam "u" (Var "t"))
skk : Term
skk = App (App sCombinator kCombinator) kCombinator
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
  putStrLn $ typeCheck sCombinator
  putStrLn $ typeCheck kCombinator
  putStrLn $ typeCheck skk
  putStrLn $ typeCheck omega
