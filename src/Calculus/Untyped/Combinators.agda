module Calculus.Untyped.Combinators where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Nat hiding (_·_)
open import Data.Fin
open import Calculus.Untyped.Base
open import Calculus.Untyped.Substitution
open import Calculus.Untyped.Progress

private
  variable
    m n l : ℕ
    M N L : Λ n

infix 9 `⟨_,_⟩

------------------------------------------------------------------------------
-- Some combinators

𝑰 𝑲 𝑻 𝑭 : Λ₀
𝑰 = ƛ 0
𝑲 = ƛ ƛ 1
𝑻 = 𝑲
𝑭 = ƛ ƛ 0

`⟨_,_⟩ : (M N : Λ n) → Λ n
`⟨ M , N ⟩ = ƛ 0 · ↑₁ M · ↑₁ N

`projₗ : Λ₀ → Λ₀
`projₗ M = M · 𝑻

`projᵣ : Λ₀ → Λ₀
`projᵣ M = M · 𝑭

------------------------------------------------------------------------------
-- Church encoding of naturals

𝕓 : Bool → Λ₀
𝕓 false = 𝑭
𝕓 true  = 𝑻

------------------------------------------------------------------------------
-- Church encoding of naturals

pre𝒄_ : ℕ → Λ 2
pre𝒄 zero    = 0
pre𝒄 (suc n) = 1 · pre𝒄 n

pre𝒄-inj : (m n : ℕ) → pre𝒄 m ＝ pre𝒄 n → m ＝ n
pre𝒄-inj zero    zero    _ = refl
pre𝒄-inj (suc m) (suc n) p = ap suc (pre𝒄-inj m n (decodeΛ $ encodeΛ p .snd))
pre𝒄-inj zero    (suc n) p = absurd (encodeΛ p)
pre𝒄-inj (suc m) zero    p = absurd (encodeΛ p)

𝒄_ : ℕ → Λ₀
𝒄 n = ƛ ƛ pre𝒄 n

pre𝒄-is-Normal : (n : ℕ) → Normal (pre𝒄 n)
pre𝒄-is-Normal zero    = ′ (` fzero)
pre𝒄-is-Normal (suc n) = ′ ((` fsuc fzero) · pre𝒄-is-Normal n)

𝒄-is-Normal : (n : ℕ) → Normal (𝒄 n)
𝒄-is-Normal n = ƛ ƛ pre𝒄-is-Normal n

𝒄-inj : (m n : ℕ) → 𝒄 m ＝ 𝒄 n → m ＝ n
𝒄-inj m n p = pre𝒄-inj m n (decodeΛ (encodeΛ p) )
------------------------------------------------------------------------------
-- Examples

β-projₗ : `projₗ `⟨ M , N ⟩ -↠ M
β-projₗ {M} {N} = begin
  (ƛ 0 · ↑₁ M · ↑₁ N) · 𝑻
    -→⟨ β ⟩
  𝑻 · ↑₁ M [ 𝑻 ]ₗ · ↑₁ N [ 𝑻 ]ₗ
    -→⟨ ξₗ β ⟩
  (ƛ 1) [ ↑₁ M [ 𝑻 ]ₗ ]ₗ · ↑₁ N [ 𝑻 ]ₗ
    ≡⟨ ap² {C = λ _ _ → Λ₀} _·_ (ap {B = λ _ → Λ₀} (ƛ_ ∘ ↑₁_) (subst-rename-∅ _ M)) (subst-rename-∅ _ N) ⟩
  (ƛ ↑₁ M) · N
    -→⟨ β ⟩
  ↑₁ M [ N ]ₗ
    ≡⟨ subst-rename-∅ _ M ⟩
  M ∎ₗ
  where open -↠-Reasoning

β-projᵣ : `projᵣ `⟨ M , N ⟩ -↠ N
β-projᵣ {M} {N} = begin
  (ƛ 0 · ↑₁ M · ↑₁ N) · 𝑭
    -→⟨ β ⟩
  𝑭 · ↑₁ M [ 𝑭 ]ₗ · ↑₁ N [ 𝑭 ]ₗ
    -→⟨ ξₗ β ⟩
  (ƛ 0) · ↑₁ N [ 𝑭 ]ₗ
    -→⟨ β ⟩
  ↑₁ N [ 𝑭 ]ₗ
    ≡⟨ subst-rename-∅ _ N ⟩
  N ∎ₗ
  where open -↠-Reasoning
