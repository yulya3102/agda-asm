module PLTize where

open import OXIj.BrutalDepTypes
open import Instructions
open Data-List
open Data-Any.Membership {A = Type} _≡_

plt-stub : ∀ {Γ Ψ} → (blk Γ) ✴ ∈ Ψ → Block Ψ {Γ = Γ} id []
plt-stub label = ↝ (jmp[ label ])

pltize-heap : HeapTypes → HeapTypes
pltize-heap (blk Γ ∷ Ψ) = blk Γ ∷ blk Γ ✴ ∷ blk Γ ∷ Ψ
pltize-heap Ψ = Ψ

pltize-⊆ : ∀ {Ψ} → Ψ ⊆ pltize-heap Ψ
pltize-⊆ = {!!}

plt : ∀ {Γ Ψ} → (blk Γ) ∈ Ψ → (blk Γ) ∈ pltize-heap Ψ
plt = {!!}

got : ∀ {Γ Ψ} → (blk Γ) ∈ Ψ → (blk Γ) ✴ ∈ pltize-heap Ψ
got = {!!}

∈-⊆ : ∀ {x A B} → x ∈ A → A ⊆ B → x ∈ B
∈-⊆ = {!!}

wk-instr : ∀ {Ψ Ψ' Γ Δ Δ'} → {ss : Δ ⊆ Δ'} → Ψ ⊆ Ψ' → Instr Ψ ss Γ → Instr Ψ' ss Γ
wk-instr = {!!}

wk-blk : ∀ {Ψ Ψ' Γ Δ Δ'} → {ss : Δ ⊆ Δ'} → Ψ ⊆ Ψ' → Block Ψ ss Γ → Block Ψ' ss Γ
wk-blk = {!!}

pltize-code : ∀ {Ψ Γ Δ Δ'} → {ss : Δ' ⊆ Δ} → Block Ψ ss Γ → Block (pltize-heap Ψ) ss Γ
pltize-code halt = halt
pltize-code (↝ (call f)) = ↝ (call (∈-⊆ f pltize-⊆))
pltize-code (↝ (jmp[_] f)) = ↝ (jmp[ ∈-⊆ f pltize-⊆ ])
pltize-code (↝ (jmp f)) = ↝ (jmp (∈-⊆ f pltize-⊆ ))
pltize-code (i ∙ b) = wk-instr pltize-⊆ i ∙ pltize-code b

data BlockSeq (Ψ : HeapTypes) {Γ : RegFileTypes} :
    {Δ : RegFileTypes} → (free : Δ ⊆ Γ) → (new : RegFileTypes) → Set where
  ⊘   : BlockSeq Ψ id []
  _∷_ : {Δ' Δ'' Δ''' new new' : RegFileTypes}
      → {ss : Δ' ⊆ Γ} → Block Ψ ss new
      → {old-ss : Δ'' ⊆ Δ'} {new-ss : Δ''' ⊆ new} → BlockSeq Ψ (⊆-++ new-ss old-ss) new' → BlockSeq Ψ (⊆-trans old-ss ss) (Δ''' ++ new')

{-

Instructions only restrict types
but they don't describe what they really do
:(

-}

NewBlkSeq : {Ψ : HeapTypes} → Set
NewBlkSeq {Ψ} = Σ RegFileTypes (λ Γ → Σ RegFileTypes (λ Δ → Σ (Δ ⊆ Γ) (λ free → Σ RegFileTypes (BlockSeq Ψ free))))

jmp[]-proof : ∀ {Ψ Γ Δ new} → {CC : CallCtx Ψ}
           → {free : Δ ⊆ Γ}
           → {A : Block Ψ free new}
           → (f : (blk Γ) ✴ ∈ Ψ)
           → loadblk Ψ (deref Ψ f) ≡ _ , _ , _ , _ , A
           → BlockEq Ψ CC A (↝ jmp[ f ])
jmp[]-proof {Ψ} {CC = CC} {A = A} f p = nl (loadblk-≡ Ψ (deref Ψ f)) eq

call-proof : ∀ {Ψ Γ} → (CC : CallCtx Ψ) → {A : NewBlk Ψ}
           → (f : (blk Γ) ∈ Ψ)
           → loadblk Ψ f ≡ A
           → exec-blk Ψ CC (↝ (call f)) ≡ ((projr CC ∷ projl CC) , A)
call-proof CC f p rewrite p = refl

proof : ∀ {Γ Ψ}
      → (f : blk Γ ∈ Ψ)
      → (cc : CallCtx (pltize-heap Ψ))
      → BlockEq (pltize-heap Ψ) cc (wk-blk pltize-⊆ (↝ (call f))) (↝ (call (plt f)))
proof {Ψ = Ψ} f ctx = cc (call-proof ctx (∈-⊆ f pltize-⊆) (loadblk-≡ (pltize-heap Ψ) (∈-⊆ f pltize-⊆))) (call-proof ctx (plt f) (loadblk-≡ (pltize-heap Ψ) (plt f))) (jmp[]-proof (got f) (loadblk-≡ (pltize-heap Ψ) (deref (pltize-heap Ψ) (got f))))
