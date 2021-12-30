{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

module Lib
    ( Symbol
    ) where

-- Basic Symbol declarations
newtype Symbol = Symbol String
newtype TypeIdentifier = TypeIdentifier Integer deriving (Eq)

-- Variable definition
newtype Variable = Variable Symbol -- TODO: Maybe variables should be indexed by integers

-- Definition of types
data SimpleType where
  SimpleType :: TypeIdentifier -> SimpleType
  TypeArrow :: SimpleType -> SimpleType -> SimpleType

data Kind where
  KindType :: Kind
  KindArrow :: Kind -> Kind -> Kind

data TypeOfKind where
  TypeOfKindType :: TypeOfKind

data InhabitableType where
  Type :: SimpleType -> InhabitableType
  Kind :: Kind -> InhabitableType
  TypeOfKind :: InhabitableType
  Sort :: InhabitableType

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

-- Equality

instance Eq SimpleType where
  SimpleType x == SimpleType y = x == y
  TypeArrow a b == TypeArrow c d = a == b && c==d
  _ == _ = False

instance Eq Kind where
  KindType == KindType = True
  KindArrow a b == KindArrow c d = a == b && c == d
  _ == _ = False

instance Eq Expression where
  (TypeExpression a) == TypeExpression b  = a == b
  _ == _ = False

instance Eq InhabitableType where
  Type a == Type b = a == b
  Kind a == Kind b =  a == b
  TypeOfKind == TypeOfKind = True
  Sort == Sort = True
  _ == _ = False

-- Definition of Contexts
-- data Declaration = Declaration Expression InhabitableType
type Declaration = TrueJudgement
data Context = Context { declarations :: [Declaration] } | Join { left :: Context, right :: Context }

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
data Judgement a b = Judgement a b


-- Utility functions
retreiveType :: Expression -> InhabitableType
retreiveType (TypeExpression t) = t
retreiveType _ = undefined 

arbitraryVariable :: Expression
arbitraryVariable = VariableExpression (Variable (Symbol "x"))

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
  if TypeExpression b == c then
    ctx :+: (Context {declarations = [arbitraryVariable ::: retreiveType a]})
      :- (arbitraryVariable ::: retreiveType a)
  else
      undefined

var _ _ = undefined