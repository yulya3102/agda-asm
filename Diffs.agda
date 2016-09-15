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
  data Diff (Γ : Ctx) : Set where
    dempty  : Diff Γ
    dchg    : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ

  dapply : (Γ : Ctx) → Diff Γ → Ctx
  dapply Γ dempty = Γ
  dapply Γ (dchg c d) = dapply (chgapply Γ c) d

  dappend : ∀ {Γ} → (d : Diff Γ)
          → Diff (dapply Γ d) → Diff Γ
  dappend dempty b = b
  dappend (dchg c a) b = dchg c (dappend a b)

  dappend-dempty-lemma : ∀ {Γ} → (d : Diff Γ)
                       → dappend d dempty ≡ d
  dappend-dempty-lemma dempty = refl
  dappend-dempty-lemma (dchg c d)
    rewrite dappend-dempty-lemma d = refl

  dappend-dapply-lemma : ∀ S → (d₁ : Diff S)
                       → (d₂ : Diff (dapply S d₁))
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

regChg : ∀ {S} → RegChg S → Diff S
regChg S = dchg (rchg S) dempty

dsChg : ∀ {S} → DataStackChg S → Diff S
dsChg S = dchg (dschg S) dempty

sChg : ∀ {S} → SmallChg S → Diff S
sChg (onlyreg r) = regChg r
sChg (onlystack d) = dsChg d
sChg (regstack r d) = dchg (rchg r) $ dchg (dschg d) dempty

csChg : ∀ S → Maybe (CallStackChg S) → Diff S
csChg S (just x) = dchg (cschg x) dempty
csChg S nothing = dempty
