module TypeReconstruction where

import Control.Monad.Except
import Control.Monad.State

data Term
  = Var String
  | Lam String Term
  | App Term Term
  | Nat Int
  | Add Term Term

instance Show Term where
  show (Var x) = x
  show (Lam x y) = "λ" ++ x ++ "." ++ show y
  show (App x y) = "(" ++ show x ++ " " ++ show y ++ ")"
  show (Nat x) = show x
  show (Add x y) = "(" ++ show x ++ "+" ++ show y ++ ")"

data Type
  = TypeVar String
  | ArrowType Type Type
  | NatType
  deriving Eq

instance Show Type where
  show (TypeVar x) = x
  show (ArrowType x y) = "(" ++ show x ++ " → " ++ show y ++ ")"
  show NatType = "ℕ"

data Error
  = UnboundVariable String
  | OccursIn Type Type

instance Show Error where
  show (UnboundVariable var) = var <> " is an unbound variable."
  show (OccursIn t1 t2) = show t1 <> " occurs in " <> show t2

main :: IO ()
main = mapM_ (\t -> do
              (putStr . show) t
              putStr " ▷ "
              (putStr . show . eval) t
              putStr " : "
              print (getStart <$> typeCheck t)) [term1,term2,term3,term4,plus1,times2,arith,omega]


-- examples
term1, term2, term3, term4, plus1, times2, arith, omega :: Term
term1 = Lam "x" $ Var "x"
term2 = App term1 $ Nat 42
term3 = Lam "y" term2
term4 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
plus1 = Lam "x" (Add (Var "x") (Nat 0))
times2 = Lam "x" (Add (Var "x") (Var "x"))
arith = Lam "f" (Lam "x" (Add (App (Var "f") (Var "x")) (Var "x")))
omega = Lam "x" (App (Var "x") (Var "x"))


data Equality = E Type Type
instance Show Equality where
  show (E t1 t2) = show t1 <> " = " <> show t2

-- | Stream (not List) of Chars starting with alpha: supply of fresh variables
varStream :: String
varStream = ['\945'..]

-- | Starting var which will be the typevar assigned to a term
startingVar :: Type
startingVar = TypeVar "α₁"

-- | Look for constraint for starting var = type of term
getStart :: [Equality] -> Type
getStart ((E t s):eqs) | t == startingVar = s
                       | s == startingVar = t
                       | otherwise = getStart eqs

-- | Run type checker
typeCheck :: Term -> Either Error [Equality]
typeCheck t = evalState (runExceptT (constraintCollection t startingVar)) (varStream, []) >>= (unify . reverse)

runConstraintCollection :: Term -> Either Error [Equality]
runConstraintCollection t = evalState (runExceptT (constraintCollection t startingVar)) (varStream, [])

-- | Collect all constraints in a term with a predetermined type variable
-- | State contains current stream and mapping from term to type variable
constraintCollection :: Term -> Type -> ExceptT Error (State (String, [(String,String)])) [Equality]
constraintCollection (Var var) t = do
  (stream, ctx) <- get
  case lookup var ctx of
    Just var' -> pure [E t (TypeVar var')]
    Nothing -> throwError $ UnboundVariable var
constraintCollection (Lam x z) t = do
  (stream, ctx) <- get
  let [a,b] = map pure $ take 2 stream
  put (drop 2 stream, (x,a):ctx)
  e <- constraintCollection z (TypeVar b)
  pure $ [E t (ArrowType (TypeVar a) (TypeVar b))] <> e
constraintCollection (App t1 t2) t = do
  (stream, ctx) <- get
  let a = pure $ head stream
  put (tail stream, ctx)
  t1 <- constraintCollection t1 (ArrowType (TypeVar a) t)
  modify $ \(s,_) -> (s,ctx)
  t2 <- constraintCollection t2 (TypeVar a)
  pure $ t1 <> t2
constraintCollection (Nat x) t = pure [E t NatType]
constraintCollection (Add t1 t2) t = do
  (stream, ctx) <- get
  t1 <- constraintCollection t1 NatType
  modify $ \(s,_) -> (s,ctx)
  t2 <- constraintCollection t2 NatType
  pure $ [E t NatType] <> t1 <> t2

-- | Robinsons Unification algorithm
unify :: [Equality] -> Either Error [Equality]
unify ((E (ArrowType t1 t2) (ArrowType s1 s2)):eqs) = unify $ [E t1 s1, E t2 s2] <> eqs
unify ((E t@(TypeVar _) s@(TypeVar _)):eqs) | t == s = unify eqs
                                            | t `inAny` eqs = (E t s:) <$> unify (map (substitute s t) eqs)
                                            | otherwise = (E t s:) <$> unify eqs
unify ((E t s@(TypeVar _)):eqs) = unify (E s t:eqs)
unify ((E NatType NatType):eqs) = unify eqs
unify ((E t NatType):eqs) = (E t NatType:) <$> if t `inAny` eqs
                                               then unify (map (substitute NatType t) eqs)
                                               else unify eqs
unify ((E t s):eqs) | t `occursIn` s = Left $ OccursIn t s
                    | t `inAny` eqs = (E t s:) <$> unify (map (substitute s t) eqs)
                    | otherwise = (E t s:) <$> unify eqs
unify [] = pure []

-- | Is Type a (Sub-)Type of another Type
occursIn :: Type -> Type -> Bool
occursIn t (ArrowType t1 t2) = t `occursIn` t1 || t `occursIn` t2
occursIn t s = t == s

inAny :: Type -> [Equality] -> Bool
inAny t = foldr (\(E t1 t2) y -> t `occursIn` t1 || t `occursIn` t2 || y) False

-- | Replace t for s in Equality
substitute :: Type -> Type -> Equality -> Equality
substitute t s (E t1 t2) = E (subst t s t1) (subst t s t2)
     where subst t s (ArrowType t1 t2) = ArrowType (subst t s t1) (subst t s t2)
           subst t s NatType = NatType
           subst t s x | s == x = t
                       | otherwise = x

-- | Bonus: Evaluation
eval :: Term -> Term
eval (Add t1 t2) = case (eval t1, eval t2) of
    (Nat 0, b) -> b
    (a, Nat 0) -> a
    (Nat a, Nat b) -> Nat $ a+b
    (a,b) -> Add a b
eval (App (Lam v t1) t2) = eval $ subst (eval t2) v t1
  where subst t s (Var s') | s == s' = t
                           | otherwise = Var s'
        subst t s (Lam v t') | s == v = Lam v t'
                             | otherwise = Lam v $ subst t s t'
        subst t s (App t1 t2) = App (subst t s t1) (subst t s t2)
        subst t s (Add t1 t2) = Add (subst t s t1) (subst t s t2)
        subst t s (Nat n) = Nat n
eval (App t1 t2) = App (eval t1) (eval t2)
eval (Lam v t) = Lam v $ eval t
eval lit = lit
