module Main where
import Data.Char
import Text.ParserCombinators.Parsec
-- import qualified Data.Map.Strict as Dict
-- import System.Random
-- import Control.Monad
data Var  = V String deriving Eq
data Term = Var Var
          | Lam Var Term
          | App Term Term
          deriving Eq
{-
deriving 源自于 
>> :t V
out => V :: String -> Var
>> :t Var
out => Var :: Var -> Term
debug => :set stop :list
debug => :step <expr>
debug => :step
debugend=> :trace
-}
instance Show Var where
  show val@(V s) = s
instance Show Term where
  show val@(Var x) = show x
  show val@(Lam x e) = "\\" ++ show x
                             ++ "."
                             ++ show e
  show val@(App f e) = "("   ++ show f
                             ++ " "
                             ++ show e
                             ++ ")"
-- Parsec 
-- type Parser a = String -> [(a,String)]
symbol :: Parser Char
symbol = oneOf $ ['a'..'z'] ++ ['A'..'Z']
parseV :: Parser Var
parseV = do
  var <- many1 symbol
  return $V var
parseVar :: Parser Term
parseVar = do
  var <- parseV
  return $Var var
parseAbst :: Parser Term
parseAbst = do
  char '\\'
  argu <- parseV
  many $char ' '
  char '.'
  many $char ' '
  body <- parseExpr
  return $Lam argu body
parseApp :: Parser Term
parseApp = do
  char '('
  function <- parseExpr
  many $char ' '
  argument <- parseExpr
  char ')'
  return $App function argument

parseExpr :: Parser Term
parseExpr =  parseVar
         <|> parseAbst
         <|> parseApp
readExpr :: String -> Term
readExpr input = case parse parseExpr "error" input of
  Left err -> Var $V ("error: " ++ show err)
  Right val -> val

-- about lambda 
freeVars :: Term -> [Var]
freeVars = aux []
  where
    aux env (Var v) | v `elem` env = [] 
                    | otherwise  = [v]
    aux env (Lam v e) = aux (v:env) e
    aux env (App f e) = (aux env f) ++ (aux env e)

boundVars :: Term -> [Var]
boundVars = aux []
  where
    aux env (Var v)   | v `elem` env = [v]
                      | otherwise    = []
    aux env (Lam v e) = aux (v:env) e
    aux env (App f e) = (aux env f) ++ (aux env e)
{-
replace all free occurrences of <name> in <body> with <argument expr>
and normal order beta reduce the new <body>
-}
isFreeVar :: Term -> Bool
isFreeVar = aux []
  where
    aux env (Var v)   | v `elem` env = False
                      | otherwise    = True
    aux env (Lam v e) = aux (v:env) e
    aux env (App f e) = (aux env f) || (aux env e)
isBoundVar :: Term -> Bool
isBoundVar expr = not $isFreeVar expr

myElem :: Var -> [(Var,Term)] -> Bool
myElem v [] = False
myElem v (x@(a,b):xs)
  | v == a = True
  | otherwise = myElem v xs
myGet  :: [(Var,Term)] -> Var -> Term
myGet (x@(a,b):xs) v 
  | v == a = b
  | otherwise = myGet xs v
{-
from wiki
Substitution, written E[V := R], is the process of replacing all free occurrences of the variable V in the expression E with expression R. Substitution on terms of the λ-calculus is defined by recursion on the structure of terms, as follows (note: x and y are only variables while M and N are any λ expression).
x[x := N]       ≡ N
y[x := N]       ≡ y, if x ≠ y
(M1 M2)[x := N] ≡ (M1[x := N]) (M2[x := N])
(λx.M)[x := N]  ≡ λx.M
(λy.M)[x := N]  ≡ λy.(M[x := N]), if x ≠ y, provided y ∉ FV(N)
-}
--                                    +--+
--                                 +--|--|--+--> \z.z
--                                 |  |  | |    => \\ look 
-- 怎么用一个管道来关联这样的形式 \x.\y.(y x)   => \y.(y \z.z)

-- (\func.\arg.(func arg) \x.x) |> [ (func,\x.x) ]
-- \arg.(func arg)  |> [ (func,\x.x) ]
-- \arg.(\x.x arg)
-- (\s.(s s) \x.x) |> [ (s,\x.x) ]
-- (s s)    |> [ (s,\x.x) ]
-- (\x.x \x.x) [ (x,\x.x) ]
-- \x.x
-- (\x.x a) |> [ (x,a) ]
-- a => 
replace :: Term -> [(Var,Term)] -> Term
replace expr [] = expr
replace var@(Var v) env 
  | v `myElem` env = env `myGet` v
  | otherwise      = var
replace lam@(Lam v b@(Var c)) env
  | v `myElem` env = body
  | otherwise      = Lam v body
  where
    body = (replace b env)
replace lam@(Lam v b@(App f a)) env
  | v `myElem` env = body
  | otherwise      = Lam v body
  where
    body = App (replace f env) (replace a env)
replace lam@(Lam v b@(Lam _ _)) env
  | v `myElem` env = body
  | otherwise      = Lam v body
  where
    body = (replace b env)
    
-- replace lam@(Lam v b) env = lam
-- \func.\argc.(func argc) [ (func,\x.x) ] => b is \argc.(func argc) ,

beta :: Term -> Term
beta app@(App lam@(Lam v b) a) = replace lam [(v,a)]
beta lam@(Lam v e) = replace lam []
beta var@(Var v)   = replace var []

myX  = (Var $V "X")
myId = (Lam (V "x") (Var $V "x"))
myApply = (Lam (V "func") (Lam (V "argc") (App (Var $V "func") (Var $V "argc"))))
mySelfApply = (Lam (V "s") (App (Var (V "s")) (Var $V "s")))
myTest = (Lam (V "x") (Lam (V "y") (Lam (V "z") (App (Var $V "x") (Var $V "y") ) ) ) ) 
myTest1 = readExpr "(\\x.(z x) \\y.y)"
myTest2 = readExpr "(\\a.\\b.b \\x.x)"

main :: IO ()
main = do
  -- putStrLn "hello world"
  -- putStrLn $ show (App (Var (V "func")) (Var (V "args")))
  -- putStrLn $ show (Lam (V "x") (Var (V "x")))
  -- putStrLn $ show (alpha_subV (V "x") (V "z") (Lam (V "x") (App (Var $V "y") (Var $V "x"))) )
  -- getLine >>= print . evalExpr . readExpr 
  -- getLine >>= print . readExpr
  -- getLine >>= print . freeVars . readExpr 
  text <- getLine
  -- getLine >>= print . beta . readExpr
  case text of 
    ":q" -> putStrLn "done."
    text -> do
      putStrLn $ "=> " ++ (show (beta $ readExpr text))
      main
