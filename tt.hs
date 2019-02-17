{-# LANGUAGE DeriveFunctor #-} 
{-# LANGUAGE DeriveAnyClass #-} 

import Data.List
import Data.Maybe
import Control.Monad
import Control.Applicative

data Prop = And Prop Prop | Not Prop | Or Prop Prop | Var String deriving (Eq)

toS :: Prop -> String
toS (And x y) = "(" ++ (toS x) ++ " && " ++ (toS y) ++ ")"
toS (Or x y) = "(" ++ (toS x) ++ " || " ++ (toS y) ++ ")"
toS (Not x) = "~" ++ (toS x)
toS (Var x) = x

instance Show Prop where
        show = toS

toLatex :: Prop -> String
toLatex (And x y) = "\\left(" ++ (toLatex x) ++ " \\wedge " ++ (toLatex y) ++ "\\right)"
toLatex (Or x y) = "\\left(" ++ (toLatex x) ++ " \\vee " ++ (toLatex y) ++ "\\right)"
toLatex (Not x) = "\\neg " ++ (toLatex x)
toLatex (Var x) = x

latexFormula :: Prop -> String
latexFormula p = "$" ++ toLatex p ++ "$"


subProps :: Prop -> [Prop]
subProps (And x y) = (And x y) : ((subProps x) ++ (subProps y))
subProps (Or x y) = (Or x y) : ((subProps x) ++ (subProps y))
subProps (Not x) = (Not x) : (subProps x)
subProps (Var x) = []

vars :: Prop -> [Prop]
vars = nub . vars'
        where
          vars' (And x y) = (vars' x) ++ (vars' y)
          vars' (Or x y) = (vars' x) ++ (vars' y)
          vars' (Not x) = vars' x
          vars' (Var x) = [Var x]

type Interp = [(String,Bool)]

{- Precondition: input list contains only Var x -}
allInterps :: [Prop] -> [Interp]
allInterps [] = []
allInterps [(Var x)] = [[(x,True)],[(x,False)]]
allInterps [_] = undefined
allInterps (x:xs) = do
        y <- allInterps [x]
        zs <- allInterps xs
        return (y ++ zs)

interpToValu :: Interp -> (String -> Bool)
interpToValu xs x = maybe False snd (find ((== x) . fst) xs)

eval :: Interp -> Prop -> Bool
eval i (And x y) = (eval i x) && (eval i y)
eval i (Or x y) = (eval i x) || (eval i y)
eval i (Not x) = not (eval i x)
eval i (Var x) = interpToValu i x

headerProps :: Prop -> [Prop]
headerProps p = nub $ (vars p) ++ (reverse $ subProps p)

underInterp :: Interp -> [Prop] -> [Bool]
underInterp i = map (eval i)

makeLine :: [String] -> String
makeLine ss = concat $ intersperse "&" ss

allInterpTable :: [Prop] -> [Interp] -> [[Bool]]
allInterpTable ps is = map (\i -> map (eval i) ps) is

texifyBoolTable :: [[Bool]] -> String
texifyBoolTable bs = (++ lineEnd) $ concat $ intersperse lineEnd $ map makeLine topbots
        where
          lineEnd = "\\\\ \\hline \n"
          topbots = (map . map) toTopBot bs
          toTopBot True = "$\\top$"
          toTopBot False = "$\\bot$"

colSpec :: Int -> String
colSpec n = bookend "|" $ intersperse '|' $ take n (repeat 'c')
        where bookend x y = x ++ y ++ x

printTable :: Prop -> IO ()
printTable p = do
        let interps = allInterps (vars p) {- list of all interpretations of p -}
        let toEvals = headerProps p {- the variables and subexpressions to be evaluated for the table-}
        let numCols = length toEvals
        let topLine = "\\hline" ++ (makeLine $ map latexFormula $ toEvals) ++ "\\\\ \\hline" {- latex expr of the table header -}
        let interpLineBools = allInterpTable toEvals interps {- table of actual bools -}
        let interpLines = texifyBoolTable interpLineBools
        putStrLn "\\begin{table}[]"
        putStrLn $ "\\begin{tabular}{" ++ (colSpec numCols) ++ "}"
        putStrLn topLine
        putStrLn interpLines
        putStrLn "\\end{tabular}"
        putStrLn "\\end{table}"
        return ()

data Tok = AND | OR | NOT | VAR String | LPAREN | RPAREN | EOF deriving (Eq,Show)

tokenize :: String -> [Tok]
tokenize ('&':'&':s) = AND : (tokenize s)
tokenize ('|':'|':s) = OR : (tokenize s)
tokenize ('~':s) = NOT : (tokenize s)
tokenize ('(':s) = LPAREN : (tokenize s)
tokenize (')':s) = RPAREN : (tokenize s)
tokenize (' ':s) = tokenize s
tokenize (x:s) = (VAR $ pure x) : (tokenize s)
tokenize [] = [EOF]

data ParseError = PE String deriving (Show)

data Parser a = P ([Tok] -> (Either ParseError a,[Tok])) deriving (Functor)

parse (P p) xs = p xs

instance Applicative Parser where
        pure = return
        (<*>) = ap 

instance Monad Parser where
        return a = P (\ts -> (Right a,ts))
        (P f) >>= g = P (\ts -> let (ma,ts') = f ts
                                in case ma of
                                        Right a -> parse (g a) ts'
                                        Left e -> (Left e, ts'))


failWith :: String -> Parser a
failWith s = P $ \ts -> (Left $ PE s, ts)

peek :: Parser Tok {- Doesn't pull anything off of the input stream-}
peek = P (\ts -> case ts of
                   [] -> (Left $ PE "Can't peek, input empty. ",ts)
                   t:_ -> (Right t,ts))

tok :: Parser Tok
tok = P (\ts -> case ts of
                  [] -> (Left $ PE "Can't get token, input empty", ts)
                  t:ts -> (Right t,ts))

eat :: Tok -> Parser ()
eat t = P $ \ts -> case ts of
                        [] -> (Left $ PE $ "Can't eat a " ++ (show t) ++ ", input empty.", ts)
                        t':ts -> if (t == t') then (Right (),ts)
                                              else (Left $ PE $ err t t',ts)
        where
          err t t' = "Expected: " ++ (show t) ++ ", got: " ++ (show t')


parseProp :: Parser Prop
parseProp = parseOr

parseOr :: Parser Prop
parseOr = do
        e <- parseAnd
        t <- peek
        case t of
             OR -> do
                     eat OR
                     e' <- parseOr
                     return $ Or e e'
             _ -> return e

parseAnd :: Parser Prop
parseAnd = do
        e <- parseAt
        t <- peek
        case t of
             AND -> do
                      eat AND
                      e' <- parseAnd
                      return $ And e e'
             _ -> return e


parseAt :: Parser Prop
parseAt = do
        t <- tok
        case t of
             NOT -> Not <$> parseAt
             LPAREN -> do
                        e <- parseProp
                        eat RPAREN
                        return e
             VAR x -> return (Var x)
             t -> failWith $ "Unexpected token while parsing atomic: " ++ (show t)

tableify :: String -> IO ()
tableify s = printTable $ either (const $ Var "fail") id $ fst $ parse parseProp $ tokenize s

