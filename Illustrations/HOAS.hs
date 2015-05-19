infixl 4 :$

data Type = Base | Arrow Type Type
data Term = Var Int | Lam Term | Term :$ Term deriving Show
data Ne a = NVar Int | NApp (Ne a) a
data Nf   = NLam Nf | NNe (Ne Nf)
data Val  = VLam (Val -> Val) | VNe (Ne Val)
type Con  = [Val]

app :: Val -> Val -> Val
app (VLam f) x = f x
app (VNe  f) x = VNe (NApp f x)

eval :: Con -> Term -> Val
eval rho (Var i)  = rho !! i
eval rho (Lam b)  = VLam (\x -> eval (x : rho) b)
eval rho (f :$ x) = app (eval rho f) (eval rho x)

quoteVal :: Int -> Val -> Nf
quoteVal i (VLam f) = NLam (quoteVal (i + 1) (f (VNe (NVar i))))
quoteVal i (VNe  x) = NNe (quoteNe i x)

quoteNe :: Int -> Ne Val -> Ne Nf
quoteNe i (NVar j)   = NVar (i - j - 1)
quoteNe i (NApp f x) = NApp (quoteNe i f) (quoteVal i x)

embedNf :: Nf -> Term
embedNf (NNe x)  = embedNe x
embedNf (NLam b) = Lam (embedNf b)

embedNe :: Ne Nf -> Term
embedNe (NVar i)   = Var i
embedNe (NApp f x) = embedNe f :$ embedNf x

norm :: Term -> Term
norm = embedNf . quoteVal 0 . eval []