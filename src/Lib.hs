{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

module Lib where

-- Basic Symbol declarations
newtype Symbol = Symbol String deriving (Eq, Show)
newtype TypeIdentifier = TypeIdentifier Integer deriving (Eq, Show)

-- Variable definition
data Variable = Variable Symbol | ArbitraryVariable Int deriving (Eq, Show) -- TODO: Maybe variables should be indexed by integers

-- Definition of types
data SimpleType where
  SimpleType :: TypeIdentifier -> SimpleType
  TypeArrow :: SimpleType -> SimpleType -> SimpleType
  deriving (Eq, Show)

data Kind where
  KindType :: Kind
  KindArrow :: Kind -> Kind -> Kind
  deriving (Eq, Show)

data InhabitableType where
  Type :: SimpleType -> InhabitableType
  Kind :: Kind -> InhabitableType
  Sort :: InhabitableType
  ProductType :: Expression -> Expression -> InhabitableType
  deriving (Eq, Show)

data Value

data TypeArrow a b = HLTypeArrow a b

-- Expression

{-
 -
 - As a note, Haskell isn't built on dependent typing and in my codde types are generated on the fly so the haskell type system can't do all the checking for me.
 -
 -}

data Expression where
  -- LambdaExpression :: VariableExpression --> Expression --> Expresion
  LambdaExpression :: { lambdaVariable :: Variable, lambdaExpression :: Expression } -> Expression
  -- Application :: LambdaExpression --> Expression --> Expresion[x := y] 
  Application :: { applicationLambda :: Expression, applicationArgument :: Expression } -> Expression
  -- VariableExpression :: Variable --> TypeExpression
  VariableExpression :: { variableVariable :: Variable } -> Expression
  -- TypeExpression :: Type --> Expression
  TypeExpression :: { typeType :: InhabitableType } -> Expression
  deriving (Eq, Show)

-- Equality


-- Definition of Contexts
-- data Declaration = Declaration Expression InhabitableType
type Declaration = TrueJudgement
data Context = Context { declarations :: [Declaration] } | Join { left :: Context, right :: Context } deriving (Eq, Show)

-- Type Aliases
-- type (:-) = Entails
type Entails = (:-)
type (:::) = Judgement
pattern (:::) :: a -> b -> Judgement a b
pattern  a ::: b = Judgement a b

type TrueJudgement = Judgement Expression Expression
type Entailment = Context :- TrueJudgement

data a :- b = a :- b deriving (Eq, Show)
data Judgement a b = Judgement a b deriving (Eq, Show)

-- Constructor Synonyms
entails :: a -> b -> a :- b
entails = (:-)

pattern (:+:) :: Context -> Context -> Context
pattern  a :+: b = Join a b

pattern (:-->) :: Expression -> Expression -> InhabitableType
pattern a :--> b = ProductType a b

pattern EmptyContext :: Context
pattern EmptyContext = Context {declarations = []}

pattern BaseContext :: [Declaration] -> Context
pattern BaseContext d = Context d

-- Utility functions
retreiveType :: Expression -> InhabitableType
retreiveType (TypeExpression t) = t
retreiveType _ = undefined

{- TODO: Check this actually works as an arbitrary variable -}
arbitraryVariable :: Context -> Expression
arbitraryVariable = VariableExpression . nextArbitraryVariable -- (Variable (Symbol "x"))

nextArbitraryVariable :: Context -> Variable
nextArbitraryVariable ctx = ArbitraryVariable (nextArbitraryIdentifier ctx)

nextArbitraryIdentifier :: Context -> Int -- TODO: Serious fixing
nextArbitraryIdentifier (Context d) = maximum (idents d) + 1
nextArbitraryIdentifier (Join left right) = max (nextArbitraryIdentifier left) (nextArbitraryIdentifier right) + 1

idents :: [Declaration] -> [Int]
idents [] = [0]
idents ((Judgement x y):xs) = ident x : ident y : idents xs

ident :: Expression -> Int
ident (VariableExpression (ArbitraryVariable n)) = n
ident _ = 0

{-
 - Introduces an arbitrary variable with a given type into a context
 - 
-}

pattern Enhance :: Context -> Int -> Expression -> Context
pattern Enhance ctx n t = ctx :+: Context {declarations = [VariableExpression (ArbitraryVariable n) ::: t]}

eq3 :: Eq a => a -> a -> a -> Bool
eq3 a b c = a == b && b == c

eq4 :: Eq a => a-> a -> a -> a -> Bool
eq4 a b c d = a == b && b == c && c == d

emptyContext :: Context
emptyContext = Context {declarations = []}


pop :: Context -> TrueJudgement
pop Context {declarations = declarations} = head declarations
pop (Join left right) = pop right

popEntailment :: Context -> Entailment
popEntailment ctx = ctx :- pop ctx

materialise :: Context -> Expression
materialise ctx = case pop ctx of
  VariableExpression (ArbitraryVariable n) ::: t -> VariableExpression (ArbitraryVariable n)
  _ -> undefined


{-
 -
 - Searches for proof of statement in Context
 -
 -}
find :: Context -> TrueJudgement -> Bool
find Context {declarations = declarations} judgement = judgement `elem` declarations
find (Join left right) judgement = find left judgement || find right judgement

enhance :: Context -> Expression -> Context
enhance ctx = Enhance ctx (nextArbitraryIdentifier ctx)

-- Inference Rules
type InferenceRule = Context -> [Entailment] -> Entailment

kindIsASort :: InferenceRule
kindIsASort ctx _ = ctx :- Judgement (TypeExpression (Kind KindType)) (TypeExpression Sort)

sortIsASort :: InferenceRule
sortIsASort ctx _ = ctx :- Judgement (TypeExpression Sort) (TypeExpression Sort)

isSort :: Context -> Expression -> Bool
isSort _ (TypeExpression t) = isSort' t
isSort ctx variable@(VariableExpression _) = find ctx (variable ::: TypeExpression Sort)
isSort _ _ = False

isSort' :: InhabitableType -> Bool
isSort' (Kind KindType) = True
isSort' Sort = True
isSort' _ = False

-- (sort)
sort :: InferenceRule
sort ctx _ = ctx :- Judgement (TypeExpression (Kind KindType)) (TypeExpression Sort)

-- (var)
{-
- If it's known that A : B, and B is some sort 
- Then it's known that (x : A):ctx :- x : A
-}
var :: InferenceRule
var ctx [gamma1 :- (a ::: b)] =
  if ctx == gamma1 && isSort ctx b then
      enhance ctx a :- (arbitraryVariable ctx ::: a)
  else
      undefined

var _ _ = undefined

-- (weak)
{-
- 
- If it's known that ctx :- (A : B) and ctx :- (C : s),
- Then (x : C) :- A : B
- 
-}
weak :: InferenceRule -- Check reference, second argument may differ
weak ctx [gamma1 :- (a ::: b), (Enhance gamma2 n t) :- (c ::: s)] =
  if eq3 ctx gamma1 gamma2 && isSort ctx s then
    enhance ctx c :- (a ::: b)
  else
    undefined
weak _ _ = undefined


-- (conv)
{- 
 - Beta reduction/conversion rule for types
 -
 - If it's know that ctx :- (a :: b) and b' is a sort
 - Then if, b == b' then a :: b'
 -
 -}
conv :: InferenceRule
conv ctx [gamma1 :- (a ::: b), gamma2 :- (b' ::: c)] =
  if eq3 ctx gamma1 gamma2 && b == b' && isSort ctx c then
    ctx :- (a ::: b')
  else undefined
  where b'' = retreiveType b'
conv _ _ = undefined

-- (form)
{-
 - If it's known that A : * and (x : A):ctx :- B : s
 - Then ctx :- (A --> B) : s
 -}
form :: InferenceRule
form ctx [gamma1 :- (a ::: TypeExpression (Kind KindType)), (Enhance gamma2 n a') :- (b ::: c)] =
  if eq3 ctx gamma1 gamma2 && a == a' && isSort ctx c then
    ctx :- (TypeExpression (a' :--> b) ::: c)
  else
    undefined
form _ _ = undefined
