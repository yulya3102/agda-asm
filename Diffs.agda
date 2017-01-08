module Diffs where

open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function

open import Core

module DiffDefinition
  {Ctx : Set}
  {Chg : Ctx → Set}
  (chgapply : (Γ : Ctx) → Chg Γ → Ctx)
  where
  data TypeDiff (Γ : Ctx) : Set where
    dempty  : TypeDiff Γ
    dchg    : (c : Chg Γ) → TypeDiff (chgapply Γ c) → TypeDiff Γ

  dapply : (Γ : Ctx) → TypeDiff Γ → Ctx
  dapply Γ dempty = Γ
  dapply Γ (dchg c d) = dapply (chgapply Γ c) d

  dappend : ∀ {Γ} → (d : TypeDiff Γ)
          → TypeDiff (dapply Γ d) → TypeDiff Γ
  dappend dempty b = b
  dappend (dchg c a) b = dchg c (dappend a b)

  dappend-dempty-lemma : ∀ {Γ} → (d : TypeDiff Γ)
                       → dappend d dempty ≡ d
  dappend-dempty-lemma dempty = refl
  dappend-dempty-lemma (dchg c d)
    rewrite dappend-dempty-lemma d = refl

  dappend-dapply-lemma : ∀ S → (d₁ : TypeDiff S)
                       → (d₂ : TypeDiff (dapply S d₁))
                       → dapply S (dappend d₁ d₂)
                       ≡ dapply (dapply S d₁) d₂
  dappend-dapply-lemma S dempty d₂ = refl
  dappend-dapply-lemma S (dchg c d₁) d₂
    = dappend-dapply-lemma (chgapply S c) d₁ d₂

module ListChg (A : Set) where
  data Chg (Γ : List A) : Set where
    chg : ∀ {τ} → τ ∈ Γ → A → Chg Γ

  chgapply : (Γ : List A) → Chg Γ → List A
  chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
  chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)

module RegDiff where

  open ListChg WordType public
  open DiffDefinition chgapply public

module StackDiff (A : Set) where
  data Chg (S : List A) : Set where
    push : (i : A) → Chg S
    pop  : ∀ {Γ S'} → S ≡ Γ ∷ S' → Chg S

  chgapply : (S : List A) → Chg S → List A
  chgapply cs (push x) = x ∷ cs
  chgapply (._ ∷ S') (pop refl) = S'

  open DiffDefinition chgapply public

module StateDiff where
  data Chg (S : StateType) : Set where
    rchg  : RegDiff.Chg (StateType.registers S) → Chg S
    dschg : StackDiff.Chg WordType (StateType.datastack S) → Chg S
    cschg : StackDiff.Chg (RegFileTypes × DataStackType)
             (StateType.callstack S) → Chg S

  chgapply : (S : StateType) → Chg S → StateType
  chgapply S (rchg x)
    = record S {
      registers = RegDiff.chgapply (StateType.registers S) x
    }
  chgapply S (dschg x)
    = record S {
      datastack = StackDiff.chgapply _ (StateType.datastack S) x
    }
  chgapply S (cschg x)
    = record S {
      callstack = StackDiff.chgapply _ (StateType.callstack S) x
    }

  open DiffDefinition chgapply public
open StateDiff public

DataStackChg : StateType → Set
DataStackChg S
  = StackDiff.Chg WordType (StateType.datastack S)

CallStackChg : StateType → Set
CallStackChg S
  = StackDiff.Chg
    (RegFileTypes × DataStackType)
    (StateType.callstack S)

RegChg : StateType → Set
RegChg S = RegDiff.Chg (StateType.registers S)

data SmallChg (S : StateType) : Set where
  onlyreg   : RegChg S → SmallChg S
  onlystack : DataStackChg S → SmallChg S
  regstack  : RegChg S → DataStackChg S → SmallChg S

regChg : ∀ {S} → RegChg S → TypeDiff S
regChg S = dchg (rchg S) dempty

dsChg : ∀ {S} → DataStackChg S → TypeDiff S
dsChg S = dchg (dschg S) dempty

sChg : ∀ {S} → SmallChg S → TypeDiff S
sChg (onlyreg r) = regChg r
sChg (onlystack d) = dsChg d
sChg (regstack r d) = dchg (rchg r) $ dchg (dschg d) dempty

csChg : ∀ {S} → Maybe (CallStackChg S) → TypeDiff S
csChg (just x) = dchg (cschg x) dempty
csChg nothing = dempty
