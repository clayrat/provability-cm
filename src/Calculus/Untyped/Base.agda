module Calculus.Untyped.Base where

open import Prelude
  hiding (_∘_)
open import Data.Empty
open import Data.Dec
open import Data.Bool
open import Data.Fin
open import Correspondences.Discrete

infixr 8  ƛ_
infixl 10 _·_

infixl 11 _[_]ₗ _⟪_⟫

------------------------------------------------------------------------------
-- Typing Rules

data Λ (n : ℕ) : 𝒰  where
  `_ : (x : Fin n) → Λ n

  ƛ_ : Λ (suc n)
     → Λ n

  _·_
    : (M N : Λ n)
    → Λ n

private
  variable
    n m l          : ℕ
    M N L M′ N′ L′ Γ Δ : Λ n

Λ₀ = Λ 0
Λ₁ = Λ 1
Λ₂ = Λ 2

count : {n i : ℕ}
  → (p : i < n) → Fin n
count {n = zero}  ()
count {n = suc n} {i = zero}       p  = fzero
count {n = suc n} {i = suc i} (s≤s p) = fsuc (count p)

instance
  fromNat∈ : Number (Λ n)
  fromNat∈ {n} = record
    { Constraint = λ i → (suc i ≤ n)
    ; fromNat    = λ i ⦃ i<n ⦄ → ` count i<n
    }

------------------------------------------------------------------------------
-- Decidable equality between α-equivalent terms

codeΛ : (M N : Λ n) → 𝒰
codeΛ (` x)   (` y)   = x ＝ y
codeΛ (ƛ M)   (ƛ N)   = codeΛ M N
codeΛ (L · M) (P · Q) = codeΛ L P × codeΛ M Q
codeΛ (` _)   _       = ⊥
codeΛ (ƛ M)   _       = ⊥
codeΛ (L · M) _       = ⊥

rΛ : (M : Λ n) → codeΛ M M
rΛ (` x)   = refl
rΛ (ƛ M)   = rΛ M
rΛ (M · N) = rΛ M , rΛ N

decodeΛ : codeΛ M N → M ＝ N
decodeΛ {M = ` x}   {` y}   c       = ap `_   c
decodeΛ {M = ƛ M}   {ƛ N}   c       = ap ƛ_   (decodeΛ c)
decodeΛ {M = _ · _} {_ · _} (c , d) = ap² _·_ (decodeΛ c) (decodeΛ d)

encodeΛ : {a b : Λ n} → a ＝ b → codeΛ a b
encodeΛ {a = a} a=b = transport (ap (codeΛ a) a=b) (rΛ a)

Λ-is-discrete : is-discrete (Λ n)
Λ-is-discrete = is-discrete-η go
  where
  go : ∀ {n} → Dec on-paths-of Λ n
  go (` x)     (` y) with x ≟ y
  ... | yes eq = yes (ap `_ eq)
  ... | no ctr = no λ eq → ctr (encodeΛ eq)
  go (` x)     (ƛ y)     = no encodeΛ
  go (` x)     (y₁ · y₂) = no encodeΛ
  go (ƛ x)     (` y)     = no encodeΛ
  go (ƛ x)     (ƛ y) with (go x y)
  ... | yes eq = yes (ap ƛ_ eq)
  ... | no ctr = no λ eq → ctr (decodeΛ (encodeΛ eq))
  go (ƛ x)     (y₁ · y₂) = no encodeΛ
  go (x₁ · x₂) (` y)     = no encodeΛ
  go (x₁ · x₂) (ƛ y)     = no encodeΛ
  go (x₁ · x₂) (y₁ · y₂) with (go x₁ y₁) | (go x₂ y₂)
  ... | yes e1 | yes e2 = yes (decodeΛ (encodeΛ e1 , encodeΛ e2))
  ... | yes e1 | no c2  = no λ e2 → c2 (decodeΛ (encodeΛ e2 .snd))
  ... | no c1  | p2     = no λ e1 → c1 (decodeΛ (encodeΛ e1 .fst))

instance
  decomp-dis-Λ : goal-decomposition (quote is-discrete) (Λ n)
  decomp-dis-Λ = decomp (quote Λ-is-discrete) []

Λ-is-set : is-set (Λ n)
Λ-is-set = is-discrete→is-set Λ-is-discrete

-- corollaries

ap-inj : {A B C D : Λ n} → A · B ＝ C · D → (A ＝ C) × (B ＝ D)
ap-inj e = let (AC , BD) = encodeΛ e in decodeΛ AC , decodeΛ BD

ap≠lam : {A B : Λ n} {C : Λ (suc n)} → A · B ≠ ƛ C
ap≠lam = encodeΛ

------------------------------------------------------------------------------
-- Variable renaming

Rename : (n m : ℕ) → 𝒰
Rename n m = Fin n → Fin m

ext : (Fin n → Fin m)
  → Fin (suc n) → Fin (suc m)
ext ρ fzero    = fzero
ext ρ (fsuc n) = fsuc (ρ n)

rename : Rename n m
  → Λ n
  → Λ m
rename ρ (` x)   = ` ρ x
rename ρ (ƛ M)   = ƛ rename (ext ρ) M
rename ρ (M · N) = rename ρ M · rename ρ N

-- ↑ᵣ_ : Γ ⊢ A
--     → Γ ⧺ Δ ⊢ A
-- ↑ᵣ M = rename ρ M
--   where
--     ρ : Rename Γ (Γ ⧺ Δ)
--     ρ (Z p) = Z p
--     ρ (S x) = S ρ x

↑_ : Λ n
    → Λ (m + n)
↑ M = rename ρ M
  where
    ρ : Rename n (m + n)
    ρ {m = zero}  x = x
    ρ {m = suc _} x = fsuc (ρ x)

↑₁_ : Λ n → Λ (suc n)
↑₁_ = ↑_

↑₂_ : Λ n → Λ (2 + n)
↑₂_ = ↑_
------------------------------------------------------------------------------
-- Substitution

Subst : ℕ → ℕ → 𝒰
Subst n m = Fin n → Λ m

exts
  : Subst n m
  → Subst (suc n) (suc m)
exts σ fzero    = ` fzero
exts σ (fsuc p) = rename fsuc (σ p)

_⟪_⟫
  : Λ n
  → Subst n m
  → Λ m
(` x)   ⟪ σ ⟫ = σ x

(ƛ M)   ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫
(M · N) ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫

subst-zero
  : Λ n
  → Subst (suc n) n
subst-zero N fzero    = N
subst-zero N (fsuc x) = ` x

_[_]ₗ
  : Λ (suc n)
  → Λ n → Λ n
M [ N ]ₗ = M ⟪ subst-zero N ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 6 _-→_
data _-→_ {n : ℕ} : (M N : Λ n) → 𝒰 where
  β : (ƛ M) · N -→ M [ N ]ₗ

  ζ :   M -→ M′
    → ƛ M -→ ƛ M′
  ξₗ
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξᵣ
    : M -→ M′
      ---------------
    → L · M -→ L · M′

private
  code→ : {M M′ N N′ : Λ n} → (r : M -→ N) (s : M′ -→ N′) → 𝒰
  code→ (β {M = L} {N = M})              (β {M = L′} {N = M′})                =
    codeΛ L L′ × codeΛ M M′
  code→ (ζ {M} {M′} r)                   (ζ {M = N} {M′ = N′} s)              =
    codeΛ M N × codeΛ M′ N′ × code→ r s
  code→ (ξₗ {L = L₁} {L′ = L₂} {M} r)     (ξₗ {L = L₁′} {L′ = L₂′} {M = M′} s) =
    codeΛ L₁ L₁′ × codeΛ L₂ L₂′ × codeΛ M M′ × code→ r s
  code→ (ξᵣ {M = L₁} {M′ = L₂} {L = M} r) (ξᵣ {M = L₁′} {M′ = L₂′} {L = M′} s) =
    codeΛ L₁ L₁′ × codeΛ L₂ L₂′ × codeΛ M M′ × code→ r s
  code→ β       _     = ⊥
  code→ (ξₗ r)  _     = ⊥
  code→ (ξᵣ r₁) _     = ⊥
  code→ (ζ r)   _     = ⊥

  toCodeΛᵣ : {M N M′ N′ : Λ n}
    → (r : M -→ N) (s : M′ -→ N′) → code→ r s → codeΛ N N′
  toCodeΛᵣ {n} (β {M} {N})    (β {M = M′} {N = N′}) (c , d)  = subst (codeΛ (M [ N ]ₗ))
    (ap² {x = M} {y = M′} _[_]ₗ (decodeΛ c) {N} {N′} (decodeΛ d)) (rΛ (M [ N ]ₗ))
  toCodeΛᵣ (ζ r)  (ζ s)  (_ , d , _)     = d
  toCodeΛᵣ (ξₗ r) (ξₗ s) (_ , c , d , _) = c , d
  toCodeΛᵣ (ξᵣ r) (ξᵣ s) (_ , c , d , _) = d , c

  toCodeΛₗ : {M N M′ N′ : Λ n}
    → (r : M -→ N) (s : M′ -→ N′) → code→ r s → codeΛ M M′
  toCodeΛₗ β       β      (c , d)         = c , d
  toCodeΛₗ (ζ r)  (ζ s)   (c , _)         = c
  toCodeΛₗ (ξₗ r₁) (ξₗ s) (c , _ , d , _) = c , d
  toCodeΛₗ (ξᵣ r₁) (ξᵣ s) (c , _ , d , _) = d , c

  r→ : (r : M -→ N) → code→ r r
  r→ (β {M} {N}) = rΛ M , rΛ N
  r→ (ζ {M} {M′} red)      = rΛ M , rΛ M′ , r→ red
  r→ (ξₗ {L = N} {L′ = N′} {M = L} red) = rΛ N , rΛ N′ , rΛ L , r→ red
  r→ (ξᵣ {M} {M′} {L} red) = rΛ M , rΛ M′ , rΛ L , r→ red

{-
 -- TODO: Show that M -→ N is discrete
 -- this will likely require fording the second index in the definition of β:
 --   β : ∀ X → X ＝ M [ N ]ₗ → (ƛ M) · N -→ X

  decode→ : {M M′ N N′ : Λ n} {r : M -→ N} {s : M′ -→ N′}
    → (c : code→ r s)
    → PathP (λ i → decodeΛ {M = M} {N = M′} (toCodeΛₗ r s c) i -→ decodeΛ {M = N} {N = N′} (toCodeΛᵣ r s c) i) r s
  decode→ {r = β}   {s = β}   (c , d)          = {!!}
  decode→ {r = ζ r} {s = ζ s} (c , d , e)      = {!!}
  decode→ {r = ξₗ r} {s = ξₗ s} (c , d , e , f) = {!!}
  decode→ {r = ξᵣ r} {s = ξᵣ s} (c , d , e , f) = {!!}

  -→-is-discrete : {M N : Λ n} → is-discrete (M -→ N)
  -→-is-discrete {n} {M} {N} = is-discrete-η (go {n} {M} {N})
    where
    go : {n : ℕ} {M N : Λ n} → Dec on-paths-of (M -→ N)
    go {n} {M = .((ƛ M1) · N1)} {N = .(M1 [ N1 ]ₗ)} (β {M = M1} {N = N1}) y = {!!}
    go {n} {.(ƛ _)} {.(ƛ _)} (ζ x) y = {!!}
    go {n} {.(_ · _)} {.(_ · _)} (ξₗ x) y = {!!}
    go {n} {.(_ · _)} {.(_ · _)} (ξᵣ x) y = {!!}
-}

------------------------------------------------------------------------------
-- Multi-step beta-reduction

module -↠-Reasoning where
  infix  4 begin_
  infix  6 _-↠_
  infixr 6 _-→⟨_⟩_ _-↠⟨_⟩_ _≡⟨_⟩_ ≡⟨⟩-syntax
  infix  7 _∎ₗ

  syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

  data _-↠_ {n : ℕ} : Λ n → Λ n → 𝒰 where
    _∎ₗ : (M : Λ n) → M -↠ M

    _-→⟨_⟩_
      : ∀ L
      → L -→ M
      → M -↠ N
        ----------
      → L -↠ N
  begin_
    : M -↠ N
    → M -↠ N
  begin M-↠N = M-↠N

  _-↠⟨_⟩_
    : ∀ L
    → L -↠ M
    → M -↠ N
    → L -↠ N
  M -↠⟨ M ∎ₗ ⟩ M-↠N                = M-↠N
  L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

  _≡⟨_⟩_
    : ∀ L
    → L ＝ M
    → M -↠ N
    → L -↠ N
  _≡⟨_⟩_ {M = M}{N = N} L L=M M-↠N = transport (ap (λ M → M -↠ N) (sym L=M)) M-↠N

  ≡⟨⟩-syntax : ∀ L → L ＝ M → M -↠ N → L -↠ N
  ≡⟨⟩-syntax = _≡⟨_⟩_

  -↠-refl : M -↠ M
  -↠-refl = _ ∎ₗ

  -↠-respect-≡ : M ＝ N → M -↠ N
  -↠-respect-≡ {M = M} {N} M=N = transport (ap (λ M → M -↠ N) (sym M=N)) (N ∎ₗ)

  -→to-↠ : M -→ N → M -↠ N
  -→to-↠ M-→N = _ -→⟨ M-→N ⟩ _ ∎ₗ

  -↠-trans
    : ∀ {L}
    → L -↠ M
    → M -↠ N
      ----------
    → L -↠ N
  -↠-trans L-↠M M-↠N = _ -↠⟨ L-↠M ⟩ M-↠N

  ƛ-cong
    : M -↠ M′
    → ƛ M -↠ ƛ M′
  ƛ-cong (M ∎ₗ)                 = ƛ M ∎ₗ
  ƛ-cong (M -→⟨ M→M₁ ⟩ M₁-↠M₂) = begin
    ƛ M
      -→⟨ ζ M→M₁ ⟩
    ƛ-cong M₁-↠M₂

  ·ₗ-cong
    : M -↠ M′
    → M · N -↠ M′ · N
  ·ₗ-cong (M ∎ₗ)               = M · _ ∎ₗ
  ·ₗ-cong (M -→⟨ M→Mₗ ⟩ Mₗ-↠M₂) =
    M · _ -→⟨ ξₗ M→Mₗ ⟩ ·ₗ-cong Mₗ-↠M₂

  ·ᵣ-cong
    : N -↠ N′
    → M · N -↠ M · N′
  ·ᵣ-cong (N ∎ₗ)                = _ · N ∎ₗ
  ·ᵣ-cong (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
    _ · N -→⟨ ξᵣ N→N₁ ⟩ ·ᵣ-cong N₁-↠N₂

  ·-cong
    : M -↠ M′
    → N -↠ N′
    → M · N -↠ M′ · N′
  ·-cong M-↠M′ N-↠N′ = begin
    _ · _
      -↠⟨ ·ₗ-cong M-↠M′ ⟩
    _ · _
      -↠⟨ ·ᵣ-cong N-↠N′ ⟩
    _ · _ ∎ₗ

  code-↠ : {M N M′ N′ : Λ n}
    → (r : M -↠ N) (s : M′ -↠ N′) → 𝒰
  code-↠ (M ∎ₗ)          (N ∎ₗ)        = codeΛ M N
  code-↠ (_ -→⟨ r ⟩ rs) (_ -→⟨ s ⟩ ss) = code→ r s × code-↠ rs ss
  code-↠ (_ ∎ₗ)          (_ -→⟨ _ ⟩ _) = ⊥
  code-↠ (_ -→⟨ _ ⟩ _)  (_ ∎ₗ)         = ⊥

open -↠-Reasoning using (_-↠_; -↠-refl; -↠-trans; -→to-↠; ·-cong; ·ₗ-cong; ·ᵣ-cong) public

trans-refl≡id : (t : M -↠ N) → -↠-trans t -↠-refl ＝ t
trans-refl≡id (_ -↠-Reasoning.∎ₗ)             = refl
trans-refl≡id (M -↠-Reasoning.-→⟨ M→N ⟩ N↠L) =
  -↠-trans (M -↠-Reasoning.-→⟨ M→N ⟩ N↠L) -↠-refl
    ＝⟨ ap (_-↠_._-→⟨_⟩_ _ _) (trans-refl≡id N↠L) ⟩
  M -↠-Reasoning.-→⟨ M→N ⟩ N↠L ∎

postulate
  -→isSet  : is-set (M -→ N)
  -↠isSet  : is-set (M -↠ N)
  ∎-isProp : is-prop (M -↠ M)

