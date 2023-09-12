module Calculus.Untyped.Substitution where

open import Prelude hiding (_∘′_)
open import Data.Fin
open import Calculus.Untyped.Base

private
  variable
    m n l   : ℕ
    M N M′ N′ : Λ n
    ρ ρ₁ ρ₂   : Rename m n
    σ σ₁ σ₂   : Subst m n

infixr 5 _⨟_

_⨟_ : Subst m n → Subst n l → Subst m l
(σ ⨟ τ) x = σ x ⟪ τ ⟫

ids : Subst n n
ids = `_

----------------------------------------------------------------------
-- Congruence rules

subst-cong
  : ((x : Fin n) → σ₁ x ＝ σ₂ x)
  → (M : Λ n)
  → M ⟪ σ₁ ⟫ ＝ M ⟪ σ₂ ⟫
subst-cong p M i = M ⟪ fun-ext p i ⟫

----------------------------------------------------------------------
-- Properties of ext

ext-comp : (ρ₁ : Rename n m) (ρ₂ : Rename m l)
  → (x : Fin (suc n))
  → (ext ρ₂ ∘ ext ρ₁) x ＝ ext (ρ₂ ∘ ρ₁) x
ext-comp ρ₁ ρ₂ fzero    = refl
ext-comp ρ₁ ρ₂ (fsuc x) = refl

----------------------------------------------------------------------
-- Properties of Rename

ren : Rename n m → Subst n m
ren ρ = ids ∘ ρ

rename=subst-ren
  : (M : Λ n)
  → rename ρ M ＝ M ⟪ ren ρ ⟫
rename=subst-ren (` x)      = refl
rename=subst-ren (M · N)    =
  ap² _·_ (rename=subst-ren M) (rename=subst-ren N)
rename=subst-ren {ρ = ρ} (ƛ M) =
  rename ρ (ƛ M)
    ＝⟨⟩
  ƛ rename (ext ρ) M
    ＝⟨ ap ƛ_ (rename=subst-ren M) ⟩
  ƛ M ⟪ ren (ext ρ) ⟫
    ＝[ i ]⟨ ƛ M ⟪ fun-ext (ren-ext ρ) i ⟫ ⟩
  ƛ M ⟪ exts (ren ρ) ⟫
    ＝⟨⟩
  (ƛ M) ⟪ ren ρ ⟫ ∎
  where
    ren-ext : (ρ : Rename n m)
      → (x : Fin (suc n)) → ren (ext ρ) x ＝ exts (ren ρ) x
    ren-ext ρ fzero    = refl
    ren-ext ρ (fsuc x) = refl

rename-comp
  : (ρ₁ : Rename n m) (ρ₂ : Rename m l)
  → {M : Λ n}
  → rename ρ₂ (rename ρ₁ M) ＝ rename (ρ₂ ∘ ρ₁) M
rename-comp ρ₁ ρ₂ {M = ` x}     = refl
rename-comp ρ₁ ρ₂ {M = M · N} i = rename-comp ρ₁ ρ₂ {M} i · rename-comp ρ₁ ρ₂ {N} i
rename-comp ρ₁ ρ₂ {M = ƛ M}     =
  rename ρ₂ (rename ρ₁ (ƛ M))
    ＝⟨⟩
  ƛ rename (ext ρ₂) (rename (ext ρ₁) M)
    ＝[ i ]⟨ ƛ rename-comp (ext ρ₁) (ext ρ₂) {M} i ⟩
  ƛ rename (ext ρ₂ ∘ ext ρ₁) M
    ＝[ i ]⟨ ƛ rename (fun-ext (ext-comp ρ₁ ρ₂) i) M ⟩
  ƛ rename (ext (ρ₂ ∘ ρ₁)) M
    ＝⟨⟩
  rename (ρ₂ ∘ ρ₁) (ƛ M) ∎

----------------------------------------------------------------------
-- punchIn: Weakening at any position

punchIn : ∀ n → Rename (n + m) (n + suc m)
punchIn zero   x         = fsuc x
punchIn (suc n)  fzero   = fzero
punchIn (suc n) (fsuc x) = fsuc (punchIn n x)

punchesIn : ∀ l → Subst n m → Subst (l + n) (l + m)
punchesIn zero       σ x     = σ x
punchesIn (suc l) σ fzero    = ` fzero
punchesIn (suc l) σ (fsuc x) = rename fsuc (punchesIn l σ x)

ext-punchIn=punchIn : (x : Fin (suc l + n))
  → ext (punchIn l) x ＝ punchIn (suc l) x
ext-punchIn=punchIn  fzero   = refl
ext-punchIn=punchIn (fsuc x) = refl

exts-punchesIn=punchesIn
  : (x : Fin (suc l + n))
  → exts (punchesIn l σ) x ＝ punchesIn (suc l) σ x
exts-punchesIn=punchesIn fzero    = refl
exts-punchesIn=punchesIn (fsuc _) = refl

S=punchIn : (x : Fin n) → fsuc x ＝ punchIn 0 x
S=punchIn x = refl

punchesIn-punchIn-comm : (σ : Subst n m)
  → (x : Fin (l + n))
  → punchesIn l (exts σ) (punchIn l x) ＝ rename (punchIn l) (punchesIn l σ x)
punchesIn-punchIn-comm {suc n} {l = zero}  σ  fzero   = refl
punchesIn-punchIn-comm {suc n} {l = zero}  σ (fsuc x) = refl
punchesIn-punchIn-comm         {l = suc l} σ fzero    = refl
punchesIn-punchIn-comm         {l = suc l} σ (fsuc p) =
  rename fsuc (punchesIn l (exts σ) (punchIn l p))
    ＝⟨ ap (rename fsuc) (punchesIn-punchIn-comm σ p) ⟩
  rename fsuc (rename (punchIn l) (punchesIn l σ p))
    ＝⟨ rename-comp (punchIn l) fsuc ⟩
  rename (fsuc ∘ punchIn l) (punchesIn l σ p)
    ＝⟨⟩
  rename (punchIn (suc l) ∘ fsuc) (punchesIn l σ p)
    ＝⟨ sym (rename-comp fsuc (punchIn (suc l))) ⟩
  rename (punchIn (suc l)) (rename fsuc (punchesIn l σ p)) ∎

punchIn-punchesIn-comm : (σ : Subst n m)
  → (M : Λ (l + n))
  → rename (punchIn l) M ⟪ punchesIn l (exts σ) ⟫ ＝ rename (punchIn l) (M ⟪ punchesIn l σ ⟫)
punchIn-punchesIn-comm σ (` x)     = punchesIn-punchIn-comm σ x
punchIn-punchesIn-comm σ (M · N) i = (punchIn-punchesIn-comm σ M i) · (punchIn-punchesIn-comm σ N i)
punchIn-punchesIn-comm {n} {m} {l} σ (ƛ M) =
  rename (punchIn l) (ƛ M) ⟪ punchesIn l (exts σ) ⟫
    ＝⟨⟩
  ƛ rename (ext (punchIn _)) M ⟪ exts (punchesIn _ (exts σ)) ⟫
    ＝[ i ]⟨ ƛ rename (fun-ext ext-punchIn=punchIn i) M ⟪ exts (punchesIn _ (exts σ)) ⟫ ⟩
  ƛ rename (punchIn (suc _)) M ⟪ exts (punchesIn _ (exts σ)) ⟫
    ＝⟨ ap ƛ_ (subst-cong exts-punchesIn=punchesIn (rename (punchIn (suc l)) M)) ⟩
  ƛ rename (punchIn (suc _)) M ⟪ punchesIn (suc _) (exts σ) ⟫
    ＝⟨ ap ƛ_ (punchIn-punchesIn-comm σ M) ⟩
  ƛ rename (punchIn (suc _)) (M ⟪ punchesIn (suc _) σ ⟫)
    ＝[ i ]⟨ ƛ rename (fun-ext ext-punchIn=punchIn (~ i)) (M ⟪ punchesIn (suc _) σ ⟫) ⟩
  ƛ rename (ext (punchIn _)) (M ⟪ punchesIn (suc l) σ ⟫)
    ＝⟨ ap (ƛ_ ∘ rename (ext (punchIn _))) (subst-cong (sym ∘ exts-punchesIn=punchesIn {l}) M) ⟩
  ƛ rename (ext (punchIn l)) (M ⟪ exts (punchesIn l σ) ⟫) ∎

rename-exts : (σ : Subst n m)
  → (M : Λ n)
  → rename fsuc M ⟪ exts σ ⟫ ＝ rename fsuc (M ⟪ σ ⟫)
rename-exts σ M =
  rename fsuc M ⟪ exts σ ⟫
    ＝[ i ]⟨ rename (fun-ext S=punchIn i) M ⟪ exts σ ⟫ ⟩
  rename (punchIn zero) M ⟪ punchesIn zero (exts σ) ⟫
    ＝⟨ punchIn-punchesIn-comm σ M ⟩
  rename (punchIn zero) (M ⟪ σ ⟫)
    ＝[ i ]⟨ rename (fun-ext S=punchIn (~ i)) (M ⟪ σ ⟫) ⟩
  rename fsuc (M ⟪ σ ⟫)
    ∎

ren-ext-comm : (ρ : Rename n m)
    → (x : Fin (suc n))
    → ren (ext ρ) x ＝ exts (ren ρ) x
ren-ext-comm ρ fzero    = refl
ren-ext-comm ρ (fsuc _) = refl

----------------------------------------------------------------------
-- Monad Laws

subst-idR : (σ : Subst n m) {x : Fin n}
  → ` x ⟪ σ ⟫ ＝ σ x
subst-idR σ = refl

subst-idL
  : (M : Λ n)
  → M ⟪ ids ⟫ ＝ M
subst-idL (` x)   = refl
subst-idL (M · N) = ap² _·_ (subst-idL M) (subst-idL N)
subst-idL (ƛ_ M)  =
  ƛ M ⟪ exts ids ⟫
    ＝[ i ]⟨ ƛ M ⟪ (λ p → exts-ids=ids p i) ⟫ ⟩
  ƛ M ⟪ ids ⟫
    ＝[ i ]⟨ ƛ subst-idL M i ⟩
  ƛ M  ∎
  where
    exts-ids=ids : (x : Fin (suc n)) → (exts ids) x ＝ ids x
    exts-ids=ids fzero    = refl
    exts-ids=ids (fsuc _) = refl

subst-assoc
  : (σ₁ : Subst n m) (σ₂ : Subst m l)
  → (M : Λ n)
  →  M ⟪ σ₁ ⟫ ⟪ σ₂ ⟫ ＝ M ⟪ σ₁ ⨟ σ₂ ⟫
subst-assoc σ₁ σ₂ (` x)   = refl
subst-assoc σ₁ σ₂ (M · N) = ap² _·_ (subst-assoc σ₁ σ₂ M) (subst-assoc σ₁ σ₂ N)
subst-assoc σ₁ σ₂ (ƛ M)   =
  (ƛ M) ⟪ σ₁ ⟫ ⟪ σ₂ ⟫
    ＝⟨⟩
  ƛ M ⟪ exts σ₁ ⟫ ⟪ exts σ₂ ⟫
    ＝[ i ]⟨ ƛ subst-assoc (exts σ₁) (exts σ₂) M i ⟩
  ƛ M ⟪ _⟪ exts σ₂ ⟫ ∘ exts σ₁ ⟫
    ＝[ i ]⟨ ƛ M ⟪ (λ p → exts-subst σ₁ σ₂ p i) ⟫ ⟩
  ƛ M ⟪ exts (σ₁ ⨟ σ₂) ⟫
    ＝⟨⟩
  (ƛ M) ⟪ σ₁ ⨟ σ₂ ⟫ ∎
  where
    exts-subst : (σ₁ : Subst n m) (σ₂ : Subst m l)
      → (x : Fin (suc n))
      → (exts σ₁ ⨟ exts σ₂) x ＝ exts (σ₁ ⨟ σ₂) x
    exts-subst σ₁ σ₂ fzero    = refl
    exts-subst σ₁ σ₂ (fsuc x) = rename-exts σ₂ (σ₁ x)

----------------------------------------------------------------------
--

rename-subst : (ρ : Rename n m) (σ : Subst m l)
  → (M : Λ n)
  →  rename ρ M ⟪ σ ⟫ ＝ M ⟪ σ ∘ ρ ⟫
rename-subst ρ σ M =
  (rename ρ M) ⟪ σ ⟫
    ＝[ i ]⟨ (rename=subst-ren {ρ = ρ} M i) ⟪ σ ⟫ ⟩
  (M ⟪ ren ρ ⟫) ⟪ σ ⟫
    ＝⟨ subst-assoc (ren ρ) σ M ⟩
  M ⟪ σ ∘ ρ ⟫
    ∎

subst-zero-S=ids : {N : Λ n}
  → (x : Fin n)
  → subst-zero N (fsuc x) ＝ ids x
subst-zero-S=ids {suc n} fzero = refl
subst-zero-S=ids {suc n} (fsuc x) = refl

subst-zero-comm : (σ : Subst n m)
  → (N : Λ n) (p : Fin (suc n))
  → (exts σ ⨟ subst-zero (N ⟪ σ ⟫)) p ＝ (subst-zero N ⨟ σ) p
subst-zero-comm σ N fzero    = refl
subst-zero-comm σ N (fsuc p) =
  (rename fsuc (σ p)) ⟪ subst-zero (N ⟪ σ ⟫) ⟫
    ＝⟨ ap (_⟪ subst-zero (N ⟪ σ ⟫) ⟫) (rename=subst-ren (σ p)) ⟩
  σ p ⟪ ren fsuc ⟫ ⟪ subst-zero (N ⟪ σ ⟫) ⟫
    ＝⟨ subst-assoc (ren fsuc) (subst-zero (N ⟪ σ ⟫)) (σ p) ⟩
  σ p ⟪ subst-zero (N ⟪ σ ⟫) ∘ fsuc ⟫
    ＝[ i ]⟨ σ p ⟪ (λ p → subst-zero-S=ids {N = N ⟪ σ ⟫} p i) ⟫ ⟩
  σ p ⟪ ids ⟫
    ＝⟨ subst-idL (σ p) ⟩
  σ p ∎

------------------------------------------------------------------------------
-- Substitution Lemma

subst-ssubst : (σ : Subst n m)
  → (M : Λ (suc n)) (N : Λ n)
  → M ⟪ exts σ ⟫ [ N ⟪ σ ⟫ ]ₗ ＝ M [ N ]ₗ ⟪ σ ⟫
subst-ssubst σ M N =
  M ⟪ exts σ ⟫ [ N ⟪ σ ⟫ ]ₗ
    ＝⟨ subst-assoc (exts σ) (subst-zero (N ⟪ σ ⟫)) M ⟩
  M ⟪ exts σ ⨟ subst-zero (N ⟪ σ ⟫) ⟫
    ＝[ i ]⟨ M ⟪ (λ p → subst-zero-comm σ N p i) ⟫ ⟩
  M ⟪ subst-zero N ⨟ σ ⟫
    ＝⟨ sym (subst-assoc (subst-zero N) σ M) ⟩
  (M ⟪ subst-zero N ⟫) ⟪ σ ⟫
    ∎

rename-ssubst : (ρ : Rename n m)
  → (M : Λ (suc n)) (N : Λ n)
  → rename (ext ρ) M [ rename ρ N ]ₗ ＝ rename ρ (M [ N ]ₗ)
rename-ssubst ρ M N =
  rename (ext ρ) M [ rename ρ N ]ₗ
    ＝⟨ ap (_⟪ subst-zero (rename ρ N) ⟫) (rename=subst-ren M) ⟩
  M ⟪ ren (ext ρ) ⟫ ⟪ subst-zero (rename ρ N) ⟫
    ＝⟨ ap _⟪ subst-zero (rename ρ N) ⟫ (subst-cong (ren-ext-comm ρ) M) ⟩
  M ⟪ exts (ren ρ) ⟫ ⟪ subst-zero (rename ρ N) ⟫
    ＝⟨ subst-cong (λ { fzero → rename=subst-ren N; (fsuc _) → refl}) (M ⟪ exts (ren ρ) ⟫) ⟩
  M ⟪ exts (ren ρ) ⟫ [ N ⟪ ren ρ ⟫ ]ₗ
    ＝⟨ subst-ssubst (ren ρ) M N ⟩
  M [ N ]ₗ ⟪ ren ρ ⟫
    ＝⟨ sym (rename=subst-ren _) ⟩
  rename ρ (M [ N ]ₗ) ∎

subst-rename-∅ : {ρ : Rename 0 n} (σ : Subst n 0) → (M : Λ 0) → rename ρ M ⟪ σ ⟫ ＝ M
subst-rename-∅ {ρ = ρ} σ M =
  rename ρ M ⟪ σ ⟫
    ＝⟨ rename-subst ρ σ M ⟩
  M ⟪ σ ∘ ρ ⟫
    ＝[ i ]⟨ M ⟪ fun-ext {f = σ ∘ ρ} {g = ids} (λ ()) i ⟫ ⟩
  M ⟪ ids ⟫
    ＝⟨ subst-idL M ⟩
  M ∎

------------------------------------------------------------------------------
-- Substitution respects reduction

module _ where
  open -↠-Reasoning

  rename-reduce
    : M -→ N
    → rename ρ M -→ rename ρ N
  rename-reduce {ρ = ρ} (β {M = M} {N}) =
    subst (rename ρ ((ƛ M) · N) -→_) (rename-ssubst ρ M N) β
  rename-reduce (ζ M-→N)  = ζ  (rename-reduce M-→N)
  rename-reduce (ξₗ M-→N) = ξₗ (rename-reduce M-→N)
  rename-reduce (ξᵣ M-→N) = ξᵣ (rename-reduce M-→N)

  rename-reduce*
    : M -↠ N
    → rename ρ M -↠ rename ρ N
  rename-reduce* (M ∎ₗ)               = -↠-refl
  rename-reduce* (L -→⟨ L-→M ⟩ M-↠N) = _ -→⟨ rename-reduce L-→M ⟩ rename-reduce* M-↠N

  subst-reduce
    : M -→ N
    → M ⟪ σ ⟫ -→ N ⟪ σ ⟫
  subst-reduce {σ = σ} (β {M = M} {N}) =
    subst ((ƛ M) ⟪ σ ⟫ · N ⟪ σ ⟫ -→_) (subst-ssubst σ M N) β
  subst-reduce (ζ M-→N)  = ζ  (subst-reduce M-→N)
  subst-reduce (ξₗ M-→N) = ξₗ (subst-reduce M-→N)
  subst-reduce (ξᵣ M-→N) = ξᵣ (subst-reduce M-→N)

  subst-reduce*
    : M -↠ N
    → M ⟪ σ ⟫ -↠ N ⟪ σ ⟫
  subst-reduce* (M ∎ₗ)               = -↠-refl
  subst-reduce* (L -→⟨ L-→M ⟩ M-↠N) = _ -→⟨ subst-reduce L-→M ⟩ subst-reduce* M-↠N

  extsσ-↠σ′ : {σ σ′ : Subst n m} → ((x : Fin n) → σ x -↠ σ′ x)
    → (x : Fin (suc n))
    → exts σ x -↠ exts σ′ x
  extsσ-↠σ′ σ-↠σ′ fzero    = -↠-refl
  extsσ-↠σ′ σ-↠σ′ (fsuc x) = rename-reduce* (σ-↠σ′ x)

  reduce-subst
    : {σ σ′ : Subst n m}
    → (M : Λ n)
    → ((x : Fin n) → σ x -↠ σ′ x)
    → M ⟪ σ ⟫ -↠ M ⟪ σ′ ⟫
  reduce-subst (` x)   σ-↠σ′ = σ-↠σ′ x
  reduce-subst (ƛ M)   σ-↠σ′ = ƛ-cong (reduce-subst M (extsσ-↠σ′ σ-↠σ′))
  reduce-subst (M · N) σ-↠σ′ = ·-cong (reduce-subst M σ-↠σ′) (reduce-subst N σ-↠σ′)

  reduce-ssubst
    : (M : Λ (suc n))
    → N -↠ N′
    → M [ N ]ₗ -↠ M [ N′ ]ₗ
  reduce-ssubst {n} {N} {N′} M N-↠N′ = reduce-subst M σ-↠σ′
    where
      σ-↠σ′ : (x : Fin (suc n)) → subst-zero N x -↠ subst-zero N′ x
      σ-↠σ′ fzero    = N-↠N′
      σ-↠σ′ (fsuc x) = -↠-refl
------------------------------------------------------------------------------
-- Special cut rule
-- TODO: Simplify these special cases

γ : (N : Λ 1) → Subst 1 1
γ N fzero = N

_∘′_ : (M N : Λ 1) → Λ 1
_∘′_ M N = M ⟪ γ N ⟫

∘-ssubst-ssubst : (L M : Λ 1) (N : Λ 0)
  → (L ∘′ M) [ N ]ₗ ＝ L [ M [ N ]ₗ ]ₗ
∘-ssubst-ssubst L M N =
  (L ∘′ M) [ N ]ₗ
    ＝⟨⟩
  L ⟪ γ M ⟫ ⟪ subst-zero N ⟫
    ＝⟨ subst-assoc (γ M) (subst-zero N) L ⟩
  L ⟪ γ M ⨟ subst-zero N ⟫
    ＝⟨ subst-cong (λ { fzero → refl}) L ⟩
  L [ M [ N ]ₗ ]ₗ
    ∎

∘′-id-left  : (M : Λ 1) → 0 ∘′ M ＝ M
∘′-id-left M = refl

∘′-id-right : (M : Λ 1) → M ∘′ 0 ＝ M
∘′-id-right M =
  M ⟪ γ 0 ⟫
    ＝⟨ subst-cong γZ=ids M ⟩
  M ⟪ ids ⟫
    ＝⟨ subst-idL M ⟩
  M ∎
  where
    γZ=ids : (x : Fin 1) → γ 0 x ＝ ids  x
    γZ=ids fzero = refl

∘′-assoc    :  (L M N : Λ 1)
  → (L ∘′ M) ∘′ N ＝ L ∘′ (M ∘′ N)
∘′-assoc L M N =
  L ⟪ γ M ⟫ ⟪ γ N ⟫
    ＝⟨ subst-assoc _ _ L ⟩
  L ⟪ γ M ⨟ γ N ⟫
    ＝⟨ subst-cong (λ { fzero → refl }) L ⟩
  L ⟪ γ (M ⟪ γ N ⟫) ⟫ ∎
  where
    γ-subst-dist : {M N : Λ 1}
      → (x : Fin 1) → γ M x ⟪ γ N ⟫ ＝ γ (M ⟪ γ N ⟫) x
    γ-subst-dist fzero = refl
