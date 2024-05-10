-- The code of the parser itself.
{-# OPTIONS --erasure #-}

module Shell.Parser where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.Nat hiding (_==_; _+_; _*_)
open import Agda.Builtin.Int
open import Agda.Builtin.List
open import Haskell.Data.Char
open import Haskell.Prim.Maybe
open import Haskell.Prim.List
open import Haskell.Prim.String
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple
open import Haskell.Prim.Eq
open import Haskell.Prim.Foldable
open import Haskell.Prim.Functor
open import Haskell.Prim.Applicative
open import Haskell.Control.Applicative
open import Haskell.Prim.Monad
open Do
open import Haskell.Prim.Int using (unsafeIntToNat)
open import Haskell.Prim using (case_of_; const; id; _$_; fromString; if_then_else_; _∷_; []; a; ⊥; _∘_)

open import Tool.Cheat
open import Algebra.SemiRing
open import Algebra.Ring
import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Decimal
open import Operator.Decidable using (_≤#_)
open import Operator.Pow
open import Shell.Exp
open import Shell.Statement

{-# FOREIGN AGDA2HS
import Prelude hiding (negate, Rational, (+), (*), (^))

import Control.Applicative
import Data.Char
import Data.Functor (void)

pos :: (Integral a, Integral b) => a -> b
pos = fromIntegral

unsafeIntToNat :: Integral a => a -> Natural
unsafeIntToNat = fromIntegral
#-}

-- I'm going to use a custom error function
-- where cheat can be used.
error : {@0 absurd : ⊥} -> String -> a
error {absurd = ()} s

-- if it returns Left err, err is the error message
record Parser (a : Set) : Set where
  constructor MkParser
  field
    runParser : String -> Either String (a × String)
open Parser public
{-# COMPILE AGDA2HS Parser newtype #-}

instance
  defaultFunctorParser : DefaultFunctor Parser
  DefaultFunctor.fmap defaultFunctorParser f p = MkParser λ str -> case (runParser p str) of
    λ where
      (Left err) -> Left err
      (Right (a , rest)) -> Right (f a , rest)
  functorParser : Functor Parser
  functorParser = record {DefaultFunctor defaultFunctorParser}
  {-# COMPILE AGDA2HS functorParser #-}

  -- I got a rendering bug while trying to solve these with default implementations.

  applicativeParser : Applicative Parser
  Applicative.pure applicativeParser a = MkParser (λ rest -> Right (a , rest))
  Applicative._<*>_ applicativeParser pf pa = MkParser (λ str -> case (runParser pf str) of
    λ where
      (Left err) -> Left err
      (Right (f , rest)) -> runParser (fmap f pa) rest)
  Applicative.super applicativeParser = functorParser
  Applicative._<*_ applicativeParser x y = const <$> x <*> y  -- simply copied from DefaultApplicative
  Applicative._*>_ applicativeParser x y = const id <$> x <*> y
  {-# COMPILE AGDA2HS applicativeParser #-}

  -- Here, we need an instance for Alternative (Either String).
  -- Either a does not work because we cannot choose a default value from a.
  {-# TERMINATING #-}
  alternativeEitherString : Alternative (Either String)
                                                 -- v string literals are for Agda's builtin String type, which is different
  Alternative.empty alternativeEitherString = Left (fromString "Alternative.empty called as Either String")
  Alternative._<|>_ alternativeEitherString (Left _) e2 = e2
  Alternative._<|>_ alternativeEitherString (Right x) _ = Right x
  Alternative.super alternativeEitherString = iApplicativeEither
  Alternative.some alternativeEitherString v = _<*>_ (fmap _∷_ v) (many v)
  Alternative.many alternativeEitherString v = some v <|> pure []
  {-# COMPILE AGDA2HS alternativeEitherString #-}

  {-# TERMINATING #-}
  alternativeParser : Alternative Parser
  Alternative.empty alternativeParser = MkParser (λ _ -> Left (fromString "Alternative.empty called as Parser"))
  Alternative._<|>_ alternativeParser (MkParser runp1) (MkParser runp2)
    = MkParser (λ str → runp1 str <|> runp2 str)
  Alternative.super alternativeParser = applicativeParser
  Alternative.some alternativeParser v = _<*>_ (fmap _∷_ v) (many v)
  Alternative.many alternativeParser v = some v <|> pure []
  {-# COMPILE AGDA2HS alternativeParser #-}

  -- but this works... hm
  defaultMonadParser : DefaultMonad Parser
  DefaultMonad._>>=_ defaultMonadParser pa f = MkParser (λ str -> case (runParser pa str) of
    λ where
      (Left err) -> Left err
      (Right (a , rest)) -> runParser (f a) rest)
  DefaultMonad.super defaultMonadParser = applicativeParser
  monadParser : Monad Parser
  monadParser = record {_>>=_ = DefaultMonad._>>=_ defaultMonadParser;
                        return = DefaultMonad.return defaultMonadParser;
                        _>>_ = DefaultMonad._>>_ defaultMonadParser;
                        _=<<_ = DefaultMonad._=<<_ defaultMonadParser}
  {-# COMPILE AGDA2HS monadParser #-}

-- Fails and provides an error message wrapped in Left.
failWith : {a : Set} -> String -> Parser a
failWith str = MkParser (const (Left str))
{-# COMPILE AGDA2HS failWith #-}

eof : Parser ⊤
eof = MkParser $ λ s -> case s of λ where
  [] -> Right (tt , [])
  _  -> Left (fromString "end-of-file expected")
{-# COMPILE AGDA2HS eof #-}

satisfy : (Char -> Bool) -> Parser Char
satisfy p = MkParser $ λ s -> case s of λ where
  (x ∷ xs) -> if p x then Right (x , xs) else Left ("character not satisfying condition: " ++ x ∷ [])
  _            -> Left (fromString "unexpected end-of-file when calling `satisfy`")
{-# COMPILE AGDA2HS satisfy #-}

anyChar : Parser Char
anyChar = satisfy $ const true
{-# COMPILE AGDA2HS anyChar #-}

char : Char -> Parser ⊤
char c = void $ satisfy (_== c)
{-# COMPILE AGDA2HS char #-}

digit : Parser Nat
digit = digitToNat <$> satisfy isDigit
  where
  digitToNat : Char → Nat
  digitToNat c = Haskell.Prim.monusNat (Haskell.Prim.Int.unsafeIntToNat (ord c)) 48
{-# FOREIGN AGDA2HS
digit :: Parser Natural
digit = (\ c -> fromIntegral (ord c) Prelude.- 48) <$> satisfy isDigit
#-}

string : String -> Parser ⊤
string = mapM₋ char
{-# COMPILE AGDA2HS string #-}

natural : Parser Nat
natural = foldl (\acc a -> acc * 10 + a) 0 <$> some digit
                                      -- ^ in theory, this will never be used, because `some` would return Left then
{-# COMPILE AGDA2HS natural #-}

-- We parse decimal fractions as rationals.
-- (Maybe we should warn the user
-- that these are only decimals...
-- e.g. that 0.333 is not 1/3 :D)
-- This can also be only non-negative,
-- as negation will be an operator.
decimal : Parser Decimal
decimal = do
  intPart <- natural
  char '.'
  right <- some (satisfy isDigit)
  case (runParser natural right) of λ where
    (Left err) -> failWith err
    (Right (fracPart , _)) -> let e = unsafeIntToNat (length right) in
        return $ MkDec
                   (pos intPart * (pos 10) ^ e
                       + pos fracPart)
                   (negate (pos e))
{-# COMPILE AGDA2HS decimal #-}

between : {left a right : Set} -> Parser left -> Parser a -> Parser right -> Parser a
between left a right -- left *> a <* right
  = do left
       a' <- a
       a' <$ right
{-# COMPILE AGDA2HS between #-}

-- For a delimited enumeration with at least one element.
sepBy1 : {a delim : Set} -> Parser a -> Parser delim -> Parser {- non-empty -} (List a)
sepBy1 a delim = _∷_ <$> a <*> many (delim *> a)
{-# COMPILE AGDA2HS sepBy1 #-}

-- For a delimited enumeration.
sepBy : {a delim : Set} -> Parser a -> Parser delim -> Parser (List a)
sepBy a delim = sepBy1 a delim <|> pure []
{-# COMPILE AGDA2HS sepBy #-}

-- For whitespace.
ws : Parser ⊤
ws = void $ many $ satisfy (_== ' ')
{-# COMPILE AGDA2HS ws #-}

-- For reading a token and consuming the whitespace after it.
tok : Parser a -> Parser a
tok p = p <* ws
{-# COMPILE AGDA2HS tok #-}

-- For parsing an entire input (with whitespace at the beginning and the end).
topLevel : Parser a -> Parser a
topLevel p = ws *> tok p <* eof
{-# COMPILE AGDA2HS topLevel #-}

-- The apostrophed versions are the ones
-- which also consume the whitespace after the tokens.

natural' : Parser Nat
natural' = tok natural
{-# COMPILE AGDA2HS natural' #-}

decimal' : Parser Decimal
decimal' = tok decimal
{-# COMPILE AGDA2HS decimal' #-}

char' : Char -> Parser ⊤
char' c = tok $ char c
{-# COMPILE AGDA2HS char' #-}

string' : String -> Parser ⊤
string' str = tok $ string str
{-# COMPILE AGDA2HS string' #-}

-- Parses a list and then foldr's it.
rightAssoc : {a sep : Set} -> (a -> a -> a) -> Parser a -> Parser sep -> Parser a
rightAssoc f a sep = foldr f (error {absurd = cheat} "foldr was called on an empty Foldable") <$> sepBy1 a sep
{-# COMPILE AGDA2HS rightAssoc #-}

-- Similarly for foldl.
leftAssoc : {a sep : Set} -> (a -> a -> a) -> Parser a -> Parser sep -> Parser a
leftAssoc f a sep = foldl f (error {absurd = cheat} "foldl was called on an empty Foldable") <$> sepBy1 a sep
{-# COMPILE AGDA2HS leftAssoc #-}

-- This only works for lists with 1 or 2 members;
-- otherwise it fails.
-- If it can only find one, this is actually equivalent to calling pa.
nonAssoc : {a sep : Set} -> (a -> a -> a) -> Parser a -> Parser sep -> Parser a
nonAssoc f pa psep = do
  exps <- sepBy1 pa psep
  case exps of λ where
    []              -> failWith (fromString "0 operands for a non-associative operator")
    (e ∷ [])        -> pure e
    (e1 ∷ e2 ∷ [])  -> pure (f e1 e2)
    _               -> failWith (fromString "more than 2 operands for a non-associative operator")
{-# COMPILE AGDA2HS nonAssoc #-}

-- Parses one or more values
-- and foldr's them with operators parsed from the string.
-- If it can only find one, this is actually equivalent to calling v.
-- The list of parsers represent the operators of equal precedence.
{-# TERMINATING #-}
chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 v op = do
    val <- v
    (do
        opr <- op
        res <- chainr1 v op
        pure (opr val res)
        ) <|> pure val
{-# COMPILE AGDA2HS chainr1 #-}

-- Same with foldl.
{-# TERMINATING #-}
chainl1 : {a : Set} -> Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 {a} v op = v >>= parseLeft v op
    where
        parseLeft : Parser a -> Parser (a -> a -> a) -> a -> Parser a
        parseLeft v op val = (do
            opr <- op
            val2 <- v
            parseLeft v op (opr val val2)) <|> pure val
{-# COMPILE AGDA2HS chainl1 #-}

-- These also consume whitespaces!

pBool : Parser Exp
pBool = BoolLit <$> (true <$ string' "True" <|> false <$ string' "False")
{-# COMPILE AGDA2HS pBool #-}

-- Contains reserved keywords and function names.
keywords : List String                                       -- v we reserve these; maybe we will use them later
keywords = "for" ∷ "if" ∷ "while" ∷ "do" ∷ "true" ∷ "false" ∷ "bool" ∷ "int" ∷ "rational" ∷ "real" ∷ "history"
         ∷ "pi" ∷ "e" ∷ "exp" ∷ "sqrt" ∷ "sin" ∷ "cos" ∷ "tg" ∷ []
{-# COMPILE AGDA2HS keywords #-}

-- Parses identifiers.
pIdent' : Parser String
pIdent' = do
  x <- some (satisfy isAlpha) <* ws
  if elem x keywords
    then failWith ("unexpected keyword \"" ++ x ++ "\"")
    else pure x
{-# COMPILE AGDA2HS pIdent' #-}

pKeyword' : String -> Parser ⊤
pKeyword' s = do
  string s
  -- if there are other letters not separated by whitespace from the keyword,
  -- then fail
  (satisfy isAlpha *> failWith ("keyword \"" ++ s ++ "\" continues with other characters")) <|> ws
{-# COMPILE AGDA2HS pKeyword' #-}

-- Parsing real constants.
pRealConst : Parser Exp
pRealConst = (Pi <$ pKeyword' "pi") <|>
             (E  <$ pKeyword' "e")
{-# COMPILE AGDA2HS pRealConst #-}

-- Parse a history reference in the form of "history[n]".
-- E.g. history[1] will be the result of the last but one statement.
pHistory' : Parser Exp
pHistory' = History <$> (pKeyword' "history" *> char' '[' *> natural' <* char' ']')
{-# COMPILE AGDA2HS pHistory' #-}

-- pAtom: Parsing anything that is considered to be atomic:
-- an integer literal, a boolean literal, a variable name,
-- a history item
-- or an expression between parantheses.
-- Here, we actually only parse integers without a negation sign,
-- as that is going to be treated as a prefix operator.
-- Note: the decimals must be checked _before_ the integers.
{-# TERMINATING #-}
pAtom pExp : Parser Exp
pAtom = (DecimalLit <$> decimal') <|>(NatLit <$>  natural') <|> pBool <|> pRealConst <|> pHistory' <|> (Var <$> pIdent') <|> between (char' '(') pExp (char' ')')
        <|> failWith "no parser matching the expression"
{-# COMPILE AGDA2HS pAtom #-}

-- Parsing real functions.
-- This has to be the last one before pAtom.
pRealFun : Parser Exp
pRealFun = (Expo <$> (pKeyword' "exp" *> pAtom)) <|>
           (Sqrt <$> (pKeyword' "sqrt" *> pAtom)) <|>
           (Sin  <$> (pKeyword' "sin" *> pAtom)) <|>
           (Cos  <$> (pKeyword' "cos" *> pAtom)) <|>
           pAtom
{-# COMPILE AGDA2HS pRealFun #-}

-- negation
pNeg : Parser Exp
pNeg = Neg <$> (char' '-' *> pRealFun) <|> pRealFun
{-# COMPILE AGDA2HS pNeg #-}

pNot : Parser Exp
pNot = Not <$> (char' '!' *> pNeg) <|> pNeg
{-# COMPILE AGDA2HS pNot #-}

-- Beware; this is infixr.
pPow : Parser Exp
pPow = chainr1 pNot (Exp.Pow <$ char' '^')
{-# COMPILE AGDA2HS pPow #-}

-- These have equal precedence.
pMulDiv : Parser Exp
pMulDiv = chainl1 pPow ((Mul <$ char' '*') <|> (Div <$ char' '/'))
{-# COMPILE AGDA2HS pMulDiv #-}

-- These too.
pAddSub : Parser Exp
pAddSub = chainl1 pMulDiv ((Add <$ char' '+') <|> (Sub <$ char' '-'))
{-# COMPILE AGDA2HS pAddSub #-}

pLt : Parser Exp
pLt = nonAssoc Lt pAddSub (char' '<')
{-# COMPILE AGDA2HS pLt #-}

pLe : Parser Exp
pLe = nonAssoc Le pLt (string' "<=")
{-# COMPILE AGDA2HS pLe #-}

pEq : Parser Exp
pEq = nonAssoc Exp.Eq pLe (string' "==")
{-# COMPILE AGDA2HS pEq #-}

pAnd : Parser Exp
pAnd = chainr1 pEq (And <$ string' "&&")
{-# COMPILE AGDA2HS pAnd #-}

pOr : Parser Exp
pOr = chainr1 pAnd (Or <$ string' "||")
{-# COMPILE AGDA2HS pOr #-}

-- Parses an expression.
-- Actually, it is an alias for
-- the operator with the least precedence.
-- pExp : Parser Exp
pExp = pOr
{-# COMPILE AGDA2HS pExp #-}

{-# TERMINATING #-}
pStatement : Parser Statement

-- Program parser
-- statements separated by semicolons
pProgram : Parser (List Statement)
pProgram = sepBy1 pStatement (char' ';')
{-# COMPILE AGDA2HS pProgram #-}

-- statement : Parser Statement
pStatement = (Assign <$> pIdent' <*> (char' '=' *> (pExp <* ws)))
  <|> If <$> (pKeyword' "if" *> (pExp <* ws)) <*> (char' '{' *> pProgram) <* char' '}'
  <|> While <$> (pKeyword' "while" *> (pExp <* ws)) <*> (char' '{' *> pProgram) <* char' '}'
  <|> Eval <$> pExp   -- a simple expression
  <|> Empty <$ ws
{-# COMPILE AGDA2HS pStatement #-}
