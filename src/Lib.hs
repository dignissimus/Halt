{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

module Lib
    ( Symbol
    ) where

-- Basic Symbol declarations
newtype Symbol = Symbol String deriving Eq
newtype TypeIdentifier = TypeIdentifier Integer deriving Eq

-- Variable definition
newtype Variable = Variable Symbol deriving Eq -- TODO: Maybe variables should be indexed by integers

-- Definition of types
data SimpleType where
  SimpleType :: TypeIdentifier -> SimpleType
  TypeArrow :: SimpleType -> SimpleType -> SimpleType
  deriving Eq

data Kind where
  KindType :: Kind
  KindArrow :: Kind -> Kind -> Kind
  deriving Eq

data TypeOfKind where
  TypeOfKindType :: TypeOfKind

data InhabitableType where
  Type :: SimpleType -> InhabitableType
  Kind :: Kind -> InhabitableType
  TypeOfKind :: InhabitableType
  Sort :: InhabitableType
  deriving Eq

data Value

data TypeArrow a b = HLTypeArrow a b
type (-->) = Entails

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
  deriving Eq

-- Equality


-- Definition of Contexts
-- data Declaration = Declaration Expression InhabitableType
type Declaration = TrueJudgement
data Context = Context { declarations :: [Declaration] } | Join { left :: Context, right :: Context } deriving Eq

-- Type Aliases
-- type (:-) = Entails
type Entails = (:-)
type (:::) = Judgement
pattern (:::) :: a -> b -> Judgement a b
pattern  a ::: b = Judgement a b

type TrueJudgement = Judgement Expression InhabitableType
type Entailment = Context :- TrueJudgement

-- Constructor Synonyms
-- (:-) = Entails
entails :: a -> b -> a :- b
entails = (:-)

pattern (:+:) :: Context -> Context -> Context
pattern  a :+: b = Join a b


-- Entailment Definition
-- As a note, the program deals only with the type Entails Context (Judgement Expression InhabitableType)
data a :- b = a :- b
data Judgement a b = Judgement a b deriving Eq


-- Utility functions
retreiveType :: Expression -> InhabitableType
retreiveType (TypeExpression t) = t
retreiveType _ = undefined 

arbitraryVariable :: Expression
arbitraryVariable = VariableExpression (Variable (Symbol "x"))
-- TODO: Check this actually works as an arbitrary variable

eq3 :: Eq a => a -> a -> a -> Bool
eq3 a b c = a == b && b == c

-- Inference Rules
type InferenceRule = Context -> [Entailment] -> Entailment

kindIsASort :: InferenceRule
kindIsASort ctx _ = ctx :- Judgement (TypeExpression (Kind KindType)) Sort

typeOfKindIsASort :: InferenceRule
typeOfKindIsASort ctx _ = ctx :- Judgement (TypeExpression TypeOfKind) Sort

-- (sort)
sort :: InferenceRule
sort ctx _ = ctx :- Judgement (TypeExpression (Kind KindType)) TypeOfKind

-- (var)
{-
- If it's known that A : B, and B is some sort 
- Then it's known that (x : A):ctx :- x : A
-}
var :: InferenceRule
var ctx [gamma1 :- (a ::: b), gamma2 :- (c ::: Sort)] =
  if eq3 ctx gamma1 gamma2 && TypeExpression b == c then
    ctx :+: (Context {declarations = [arbitraryVariable ::: retreiveType a]})
      :- (arbitraryVariable ::: retreiveType a)
  else
      undefined

var _ _ = undefined

-- (weak)
{-
- If it's known that ctx :- (A : B) and ctx :- (C : s) then
  (x : C) :- A : B
- 
-}
weak :: InferenceRule
weak ctx [gamma1 :- (a ::: b), gamma2 :- (c ::: Sort)] = 
  if eq3 ctx gamma1 gamma2 then
    ctx :+: (Context {declarations = [arbitraryVariable ::: retreiveType c]})
      :- (a ::: b)
  else
    undefined
weak _ _ = undefined 