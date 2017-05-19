{-# LANGUAGE FlexibleInstances #-}
import Prelude
import Data.List

data Expr =
    Var String
  | Const String
  | Lambda String Expr
  | App Expr Expr

data ExprB =
    VarB Int
  | ConstB String
  | LambdaB ExprB
  | AppB ExprB ExprB
  deriving (Eq)

(==>) = Lambda
infixr 5 ==>

(@@) = App
infixl 6 @@

instance Show Expr where
    showsPrec x (Var v) = (v ++)
    showsPrec x (Const v) = (showsPrec x v)
    showsPrec x (Lambda v e) = (v ++)
                             . ("==>" ++)
                             . (showsPrec x e)
    showsPrec x (App a b) = ("(" ++)
                          . (showsPrec x a)
                          . (") @@ (" ++)
                          . (showsPrec x b)
                          . (")" ++)

instance Show ExprB where
    showsPrec x (VarB v) = (showsPrec x v)
    showsPrec x (ConstB v) = (showsPrec x v)
    showsPrec x (LambdaB e) = ("l."++) . (showsPrec x e)
    showsPrec x (AppB a b) = ("(" ++)
                          . (showsPrec x a)
                          . (") @@ (" ++)
                          . (showsPrec x b)
                          . (")" ++)

toDeBruijnIndex :: Expr -> ExprB
toDeBruijnIndex e = go' e []
  where
    go' :: Expr -> [String] -> ExprB
    go' (Var v) vs = let Just i = elemIndex v vs in VarB i
    go' (Const v) vs = ConstB v
    go' (Lambda v e) vs = LambdaB (go' e (v:vs))
    go' (App a b) vs = AppB (go' a vs) (go' b vs)

allStrings = [ c : s | s <- "" : allStrings, c <- ['a'..'z'] ]


fromDeBruijnIndex :: ExprB -> Expr
fromDeBruijnIndex e = go' e [] allStrings
  where
    go' :: ExprB -> [String] -> [String] -> Expr
    go' (VarB i) ns _ = Var (getVarName i ns)
    go' (ConstB v) _ _ = Const v
    go' (LambdaB e) ns (n:ns') = Lambda n (go' e (n:ns) ns')
    go' (AppB a b) ns ns' = (go' a ns ns') @@ (go' b ns ns')

    getVarName :: Int -> [String] -> String
    getVarName 0 (n:_) = n
    getVarName x [] = '_':(show x)
    getVarName x (_:ns) = getVarName (x - 1) ns

church :: Int -> Expr
church 0 = "s" ==> "z" ==> Var "z"
church n = "s" ==> "z" ==> Var "s" @@ ((church $ n-1) @@ Var "s" @@ Var "z")

churchS = "x" ==> "s" ==> "z" ==> Var "s" @@ (Var "x" @@ Var "s" @@ Var "z")
churchSum = "a" ==> "b" ==> "s" ==> "z" ==> (Var "a" @@ Var "s") @@ ((Var "b" @@ Var "s" @@ Var "z"))
churchMul = "a" ==> "b" ==> "s" ==> (Var "a" @@ (Var "b" @@ Var "s"))

data Value e =
    ConstV String
  | AppConstV String (Value e)
  | FunV e (Context e)
  deriving Show
type Context e = [Value e]

unfoldValueB :: Value ExprB -> ExprB
unfoldValueB (ConstV s) = ConstB s
unfoldValueB (AppConstV s v) = AppB (ConstB s) (unfoldValueB v)
unfoldValueB (FunV e ctx) = LambdaB (subst e (Nothing:map (Just . unfoldValueB) ctx))
  where
    subst :: ExprB -> [Maybe ExprB] -> ExprB
    subst (VarB x) ctx =
        case ctx !! x of
        Just v -> v
        Nothing -> VarB x
    subst (ConstB s) _ = ConstB s
    subst (LambdaB e) ctx = LambdaB (subst e (Nothing:ctx))
    subst (AppB e1 e2) ctx = AppB (subst e1 ctx) (subst e2 ctx)

valueBToValue :: Value ExprB -> Value Expr
valueBToValue (ConstV v) = ConstV v
valueBToValue (AppConstV v e) = AppConstV v (valueBToValue e)
valueBToValue (FunV e c) = FunV (fromDeBruijnIndex e) (map valueBToValue c)

computeb :: ExprB -> Value ExprB
computeb e = computeb' [] e

computeb' :: Context ExprB -> ExprB -> Value ExprB
computeb' c (VarB i) = c !! i
computeb' c (ConstB v) = ConstV v
computeb' c (LambdaB f) = FunV f c
computeb' c (AppB a b) =
    let v = computeb' c b in
    case computeb' c a of
        (FunV a' c') -> computeb' (v:c') a'
        (ConstV a') -> AppConstV a' v

fromChurch :: Value ExprB -> Int
fromChurch = fromChurch' Nothing 
  where
    fromChurch' :: Maybe String -> Value ExprB -> Int
    fromChurch' Nothing (ConstV _) = 0
    fromChurch' Nothing (AppConstV f e) = (fromChurch' (Just f) e) + 1
    fromChurch' (Just f0) (ConstV f) | f0 /= f = 0
    fromChurch' (Just f0) (AppConstV f e) | f0 == f = (fromChurch' (Just f0) e) + 1
    
computeChurch :: Expr -> Int
computeChurch e = fromChurch $ computeb $ toDeBruijnIndex $ e @@ Const "f" @@ Const "z"

debug1 = do
    let l = "x" ==> ("x" ==> Var "x") @@ ("z" ==> Var "z" @@ Var "x" @@ Const "foo")
    print $ l
    print $ toDeBruijnIndex l
    print $ fromDeBruijnIndex (toDeBruijnIndex l)

debug2 = do
    print $ (church 0)
    print $ churchS @@ (church 0)
    print $ toDeBruijnIndex $ churchS @@ (church 0)
    print $ computeb $ toDeBruijnIndex $ churchS @@ (church 0)
    print $ fromDeBruijnIndex $ unfoldValueB $ computeb $ toDeBruijnIndex $ churchS @@ (church 0)
    print $ fromDeBruijnIndex $ unfoldValueB $ computeb $ toDeBruijnIndex $ churchS @@ (church 0) @@ Const "f"
    print $ fromDeBruijnIndex $ unfoldValueB $ computeb $ toDeBruijnIndex $ churchS @@ (church 0) @@ Const "f" @@ Const "z"

debug3 = do
    print $ computeb $ toDeBruijnIndex $ churchMul @@ (church 2) @@ (church 4) @@ Const "f" @@ Const "z"
    print $ computeChurch $ churchMul @@ (church 2) @@ (church 4)
    print $ computeChurch $ churchMul @@ (churchMul @@ (church 2) @@ (church 4)) @@ (church 10)

main = do
    debug1
    debug2
    debug3
