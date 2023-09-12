module Calculus.Untyped.Quoting where

open import Prelude
open import Data.Empty
open import Data.Fin
open import Calculus.Untyped.Base
open import Calculus.Untyped.Progress
  using (Normal)
open import Calculus.Untyped.Combinators
open import Calculus.Untyped.Substitution
open import Calculus.Untyped.Confluence

private
  variable
    m n l : ℕ
    L M N F : Λ n

record Quoting : 𝒰 where
  field
    ⌜_⌝ₗ          : Λ n → Λ₀

    -- ⌜-⌝ reflects equality
    ⌜⌝-injective : ⌜ M ⌝ₗ ＝ ⌜ N ⌝ₗ → M ＝ N
    ⌜⌝-normal    : Normal ⌜ M ⌝ₗ

    -- ⊢ □ (A → B) ⇒ □ A ⇒ □ B
    App    : Λ 2
    App-↠  : App ⟪ exts (subst-zero ⌜ M ⌝ₗ) ⟫ [ ⌜ N ⌝ₗ ]ₗ -↠ ⌜ M · N ⌝ₗ
    -- Sub : Λ₀
    Sub   : Λ₀
    Sub-↠ : Sub · ⌜ M ⌝ₗ · ⌜ N ⌝ₗ -↠ ⌜ M [ N ]ₗ ⌝ₗ

    -- ⊢ □ A `→ □ (□ A)
    Quote   : Λ₁
    Quote-↠ : Quote [ ⌜ M ⌝ₗ ]ₗ -↠ ⌜ ⌜ M ⌝ₗ ⌝ₗ

    Eval : Λ₁
    Eval-↠ : Eval [ ⌜ M ⌝ₗ ]ₗ -↠ M

  open -↠-Reasoning
  -- ⊢ □ A `→ □ (□ A)
  Ap : Λ₀
  Ap = ƛ ƛ App
  Ap-↠ : Ap · ⌜ M ⌝ₗ · ⌜ N ⌝ₗ -↠ ⌜ M · N ⌝ₗ
  Ap-↠ {_} {M} {N} = begin
    Ap · ⌜ M ⌝ₗ · ⌜ N ⌝ₗ
      -→⟨ ξₗ β ⟩
    (ƛ App) [ ⌜ M ⌝ₗ ]ₗ · ⌜ N ⌝ₗ
      -→⟨ β ⟩
    App ⟪ exts (subst-zero ⌜ M ⌝ₗ) ⟫ [ ⌜ N ⌝ₗ ]ₗ
      -↠⟨ App-↠ ⟩
    ⌜ M · N ⌝ₗ ∎ₗ

  Num : Λ₀
  Num = ƛ Quote

  Num-↠ : Num · ⌜ M ⌝ₗ -↠ ⌜ ⌜ M ⌝ₗ ⌝ₗ
  Num-↠ {M = M} = begin
    Num · ⌜ M ⌝ₗ
      -→⟨ β ⟩
    Quote [ ⌜ M ⌝ₗ ]ₗ
      -↠⟨ Quote-↠ ⟩
    ⌜ ⌜ M ⌝ₗ ⌝ₗ ∎ₗ

  I·I≠I : 𝑰 · 𝑰 ≠ 𝑰
  I·I≠I = encodeΛ

  quoting′-not-definable : ¬ (Σ[ Q ꞉ Λ₁ ] (Π[ M ꞉ Λ₀ ] (Q [ M ]ₗ -↠ ⌜ M ⌝ₗ)) )
  quoting′-not-definable (Q , QM-↠⌜M⌝) = I·I≠I (⌜⌝-injective (Normal⇒Path ⌜⌝-normal ⌜⌝-normal (QM-↠⌜M⌝ (𝑰 · 𝑰)) QII-↠⌜I⌝))
    where
      QII-↠⌜I⌝ : Q [ 𝑰 · 𝑰 ]ₗ -↠ ⌜ 𝑰 ⌝ₗ
      QII-↠⌜I⌝ = begin
        Q [ 𝑰 · 𝑰 ]ₗ
          -↠⟨ reduce-ssubst Q (-→to-↠ β) ⟩
        Q [ 𝑰 ]ₗ
          -↠⟨ QM-↠⌜M⌝ 𝑰 ⟩
        ⌜ 𝑰 ⌝ₗ ∎ₗ

  -- ⊢ □ (ℕ `→ A) `→ □ A
  Diag : Λ₀
  Diag = ƛ ↑ Ap · 0 · (↑ Num · 0)

  Diag-↠ : Diag · ⌜ M ⌝ₗ -↠ ⌜ M · ⌜ M ⌝ₗ ⌝ₗ
  Diag-↠ {M = M} = begin
      Diag · ⌜ M ⌝ₗ
    -→⟨ β ⟩
      ↑ Ap [ ⌜ M ⌝ₗ ]ₗ · ⌜ M ⌝ₗ · (↑ Num [ ⌜ M ⌝ₗ ]ₗ · ⌜ M ⌝ₗ)
    ≡⟨ ap² (λ N L → N · ⌜ M ⌝ₗ · (L · ⌜ M ⌝ₗ)) (subst-rename-∅ _ Ap) (subst-rename-∅ _ Num) ⟩
      Ap · ⌜ M ⌝ₗ · (Num · ⌜ M ⌝ₗ)
    -↠⟨ ·ᵣ-cong Num-↠ ⟩
      Ap · ⌜ M ⌝ₗ · ⌜ ⌜ M ⌝ₗ ⌝ₗ
    -↠⟨ Ap-↠ ⟩
      ⌜ M · ⌜ M ⌝ₗ ⌝ₗ ∎ₗ

  U : Λ₀
  U = ƛ ƛ 1 · (↑ Diag · 0)

  -- the β-redex is for (∅ ⊢ igfix A · ⌜ M ⌝ -↠ ⌜ gfix M ⌝) to be true
  W : Λ₀ → Λ₀
  W F = U · F
  -- ⊢ □ A `→ A   `→   ⊢ A

  gfix : Λ₀ → Λ₀
  gfix F = W F · ⌜ W F ⌝ₗ

  gfix-↠ : gfix F -↠ F · ⌜ gfix F ⌝ₗ
  gfix-↠ {F = F} = begin
      W F · ⌜ W F ⌝ₗ
    -→⟨ ξₗ β ⟩
      (ƛ ↑ F · (↑ Diag ⟪ _ ⟫ · 0)) · ⌜ W F ⌝ₗ
    -→⟨ β ⟩
      ↑ F [ ⌜ W F ⌝ₗ ]ₗ · (↑ Diag ⟪ _ ⟫ [ ⌜ W F ⌝ₗ ]ₗ · ⌜ W F ⌝ₗ)
    ≡⟨ ap² _·_ (subst-rename-∅ _ F) (ap (_· ⌜ W F ⌝ₗ) (subst-assoc _ _ (↑ Diag) ∙ subst-rename-∅ _ Diag)) ⟩
      F · (Diag · ⌜ W F ⌝ₗ)
    -↠⟨ ·ᵣ-cong Diag-↠ ⟩
      F · ⌜ W F · ⌜ W F ⌝ₗ ⌝ₗ ∎ₗ

  sfix : Λ₁ → Λ₀
  sfix F = gfix (ƛ F)

  sfix-↠ : sfix F -↠ F [ ⌜ sfix F ⌝ₗ ]ₗ
  sfix-↠ {F = F} = begin
    sfix F
      -↠⟨ gfix-↠ ⟩
    (ƛ F) · ⌜ gfix (ƛ F) ⌝ₗ
      -→⟨ β ⟩
    F [ ⌜ sfix F ⌝ₗ ]ₗ
      ∎ₗ
  igfix : Λ₁
  igfix = ↑ Diag · (↑ Ap · ↑ ⌜ U ⌝ₗ · 0)

  igfix-↠ : {M : Λ₀} → igfix [ ⌜ M ⌝ₗ ]ₗ -↠ ⌜ gfix M ⌝ₗ
  igfix-↠ {M} = begin
    ↑ Diag [ ⌜ M ⌝ₗ ]ₗ · (↑ Ap [ ⌜ M ⌝ₗ ]ₗ · ↑ ⌜ U ⌝ₗ [ ⌜ M ⌝ₗ ]ₗ · ⌜ M ⌝ₗ)
      ≡⟨ ap² _·_ (subst-rename-∅ _ Diag) (ap (_· ⌜ M ⌝ₗ) (ap² _·_ (subst-rename-∅ _ Ap) (subst-rename-∅ _ ⌜ U ⌝ₗ))) ⟩
    Diag · (Ap · ⌜ U ⌝ₗ · ⌜ M ⌝ₗ)
      -↠⟨ ·ᵣ-cong Ap-↠  ⟩
    Diag · ⌜ W M ⌝ₗ
      -↠⟨ Diag-↠ ⟩
    ⌜ W M · ⌜ W M ⌝ₗ ⌝ₗ ∎ₗ

  -- -- ⊢ □ A `→ A   `→   ⊢ A `→ A   `→   ⊢ A
  -- selfEval`→fixpoint
  --   : Σ[ e ∈ ∅ ⊢ nat `→ A ] (∀ a → ∅ ⊢ e · ⌜ a ⌝ -↠ a)
  --   → (f : ∅ ⊢ A `→ A)
  --   → Σ[ a ∈ ∅ ⊢ A ] (∅ ⊢ a -↠ f · a)
  -- selfEval`→fixpoint {A = A} (e , e-⌜⌝-id) f = gfix f∘e ,
  --   (begin
  --     gfix f∘e
  --   -↠⟨ gfix-spec ⟩
  --     f∘e · ⌜ gfix f∘e ⌝
  --   -→⟨ β-ƛ· ⟩
  --     ↑ f ⟪ _ ⟫ · (↑ e ⟪ _ ⟫ · ⌜ gfix f∘e ⌝)
  --   ≡⟨ P.cong₂ (λ M N → M · (N · ⌜ gfix (ƛ ↑ f · (↑ e · # 0)) ⌝)) (subst-↑ _ f) (subst-↑ _ e) ⟩
  --     f · (e · ⌜ gfix f∘e ⌝)
  --   -↠⟨ ·₂-↠ (e-⌜⌝-id (gfix f∘e))  ⟩
  --     f · gfix (f∘e)
  --   ∎)
  --   where
  --     open -↠-Reasoning
  --     f∘e : ∅ ⊢ nat `→ A
  --     f∘e = ƛ ↑ f · (↑ e · # 0)

  -- -- ¬ ∀ A. □ A → A
  -- ¬∃selfEval : (∀ A → Σ[ e ∈ ∅ ⊢ nat `→ A ] (∀ a → ∅ ⊢ e · ⌜ a ⌝ -↠ a)) → ⊥
  -- ¬∃selfEval e with selfEval`→fixpoint (e nat) (ƛ suc (# 0))
  -- ... | a , a-↠suca = {! !}

  -- rice
  --   : (d : ∅ ⊢ nat `→ nat) (a b : ∅ ⊢ A)
  --   → ((x y : ∅ ⊢ A) → ∅ ⊢ x -↠ y → ∅ ⊢ d · ⌜ x ⌝ -↠ d · ⌜ y ⌝)
  --   → ∅ ⊢ d · ⌜ a ⌝ -↠ zero
  --   → ∅ ⊢ d · ⌜ b ⌝ -↠ (suc zero)
  --   → ⊥
  -- rice d a b d-ext da-↠0 db-↠1 = {! d · gfix (ƛ n → ) !} where
  --   -- r = λ n. if d n then a else b
  --   -- gnum r = gnum (λ x y n. if d n then x else y) `app` ()
  --   --    d (gfix r)
  --   -- -↠ d (gnum (r · (gfix r))
  --   -- -↠ d (gnum (if d (gfix r) then a else b))
  --   -- -↠ { d ⌜ a ⌝ -↠ 0   if d (gfix r) -↠ 1
  --   --    ; d (gnum b) -↠ 1   if d (gfix r) -↠ 0

