module Assembly.Properties where

open import Prelude
  hiding (_∘_; _∘′_; id)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat hiding (_·_)
open import Data.Fin
--open import Correspondences.Discrete hiding (_⇒_)
open import Calculus.Untyped as Λ
  hiding (`⟨_,_⟩)

open import Assembly.Base

private
  variable
    ℓ : Level
    X Y Z : Asm ℓ

∘-id : {f : Trackable X Y} → f ∘ (id X) ＝ f
∘-id {X = X} {Y} {f , F , F⊩f} i = (λ x → f x) , Fx=F i , λ {M} {x} r → lem {M} {x} r i
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)
    Fx=F : (F ∘′ 0) ＝ F
    Fx=F = ∘′-id-right F

    postulate
      lem : {M : Λ₀} {x : ⟨ X ⟩} (r : M X.⊩ x)
        → PathP (λ i → Fx=F i [ M ]ₗ Y.⊩ f x) (subst (Y._⊩ (f x)) (sym $ ∘-ssubst-ssubst F 0 M) (F⊩f r)) (F⊩f r)

id-∘ : {f : Trackable X Y} → id Y ∘ f ＝ f
id-∘ {X = X} {Y} {f , F , F⊩f} i = (λ x → f x) , F , λ {M} {x} r → lem {M} {x} r i
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)
    xF=F : 0 ∘′ F ＝ F
    xF=F = refl

    postulate
      lem : {M : Λ₀} {x : ⟨ X ⟩} (r : M X.⊩ x)
        → Path (F [ M ]ₗ Y.⊩ f x) (subst (Y._⊩ (f x)) (sym $ ∘-ssubst-ssubst 0 F M) (F⊩f r)) (F⊩f r)

∇_ : (X : Set ℓ) → Asm ℓ
∇_ {ℓ} X = X , (λ _ _ → Lift ℓ ⊤) , record
  { ⊩-respects-↠ = λ _ _ → lift tt
  ; ⊩-right-total = λ _ → ∣ 𝑰 , (lift tt) ∣₁
  ; ⊩-isSet = is-set-β hlevel!
  }

𝔹ₐ : Asm₀
𝔹ₐ = (el Bool hlevel!) , (λ M b → M -↠ 𝕓 b) , record
  { ⊩-respects-↠  = -↠-trans
  ; ⊩-right-total = λ b → ∣ 𝕓 b ,  -↠-refl ∣₁
  ; ⊩-isSet       = is-set-β -↠isSet
  }

_⊩ℕ_ : Λ₀ → ℕ → 𝒰
M ⊩ℕ n = M -↠ 𝒄 n

ℕₐ : Asm₀
ℕₐ = (el ℕ hlevel!) , (λ M n → M -↠ 𝒄 n) , record
  { ⊩-respects-↠  = -↠-trans
  ; ⊩-right-total = λ n → ∣ 𝒄 n , -↠-refl ∣₁
  ; ⊩-isSet       = is-set-β -↠isSet
  }

-- Proposition: The set Λ₀ of lambda terms is equipped with an assembly structure.
Λ₀ₐ : Asm₀
Λ₀ₐ = (el Λ₀ Λ-is-set) , (λ M N → M -↠ N) , record
  { ⊩-respects-↠  = -↠-trans
  ; ⊩-right-total = λ M → ∣ M , -↠-refl ∣₁
  ; ⊩-isSet       = is-set-β -↠isSet
  }


--CT+FunExt : ((f : ℕ → ℕ) → Σ[ F ∶ Λ₀ ] (∀ {n M} → M ⊩ℕ n → (F · M) ⊩ℕ f n))
--  → (f : ℕ → ℕ) → Dec ((n : ℕ) → f n ≡ 0)
--CT+FunExt G f with G f .fst ≟ G (λ _ → 0) .fst
--... | no ¬p = no  λ h → ¬p (cong (λ g → G g .fst) (funExt h))
--... | yes p = yes λ n → 𝒄-inj′ (Gf .fst · 𝒄 n) (f n) 0 (Gf .snd -↠-refl)
--  (subst (λ M → M · (𝒄 n) -↠ 𝒄 0) (sym p) (G0 .snd -↠-refl))
--  where
--    open Λ.Progress
--    G0 = G (λ _ → 0)
--    Gf = G f
--    𝒄-inj′ : (M : Λ₀) (m n : ℕ) → M -↠ 𝒄 m → M -↠ 𝒄 n → m ≡ n
--    𝒄-inj′ M m n p q = 𝒄-inj m n (Normal⇒Path (𝒄-is-Normal m) (𝒄-is-Normal n) p q)


------------------------------------------------------------------------------
-- Finality
⊤ₐ : Asm ℓ
⊤ₐ {ℓ} = (el (Lift ℓ ⊤) hlevel!) , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respects-↠
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isSet       = is-set-β (Lift-is-of-hlevel 2 -↠isSet)
  }
  where
    _⊩_ : Λ₀ → Lift ℓ ⊤ → 𝒰 ℓ
    M ⊩ _ = Lift ℓ (M -↠ 𝑰)

    ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
    ⊩-respects-↠ M-↠M′ (lift M′-↠𝑰) = lift (-↠-trans M-↠M′ M′-↠𝑰)

    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total _ = ∣ 𝑰 , lift -↠-refl ∣₁

module Final {X : Asm ℓ} where
  open AsmStr (str X)
  open -↠-Reasoning

  universality : Trackable X ⊤ₐ
  universality = (λ _ → lift tt) , (↑ 𝑰) , λ _ → lift -↠-refl

  global-element′ : (x : ⟨ X ⟩) → MerelyTrackable ⊤ₐ X
  global-element′ x = (λ _ → x) , ∥-∥₁.rec!
    (λ { (M , r) → ∣ ↑ M , (λ { _ → ⊩-respects-↠
      (begin ↑ M [ _ ]ₗ ≡⟨ subst-rename-∅ _ _ ⟩ M ∎ₗ) r}) ∣₁})
    (⊩-right-total x)

  global-element : (M : Λ₀) → (x : ⟨ X ⟩) → M ⊩ x
    → Trackable ⊤ₐ X
  global-element M x M⊩x = (λ _ → x) , (↑ M) , λ _ → ⊩-respects-↠ (↑ M [ _ ]ₗ ≡⟨ subst-rename-∅ _ M ⟩ M ∎ₗ ) M⊩x

  separator : (f g : Trackable X Y)
    → ((x : Trackable ⊤ₐ X) → f ∘ x ∼ g ∘ x)
    → f ∼ g
  separator {Y = Y} f g fx=gx x = ∥-∥₁.rec
    (is-of-hlevel-β 0 hlevel! (f .fst x) (g .fst x))
    (λ { (M , r) → fx=gx (global-element M x r) _ })
    (⊩-right-total x)
    where
      module Y = AsmStr (str Y)

  separator′ : (f g : Trackable X Y)
    → ((M : Λ₀) {x : ⟨ X ⟩} (r : M ⊩ x) → f ∘ global-element M x r ∼ g ∘ global-element M x r)
    → f ∼ g
  separator′ {Y = Y} f g fx=gx x = ∥-∥₁.rec
    (is-of-hlevel-β 0 hlevel! (f .fst x) (g .fst x))
    (λ { (M , r) → fx=gx M r _})
    (⊩-right-total x)

*→Λ : (M : Λ₀) → Trackable ⊤ₐ Λ₀ₐ
*→Λ M = Final.global-element M M -↠-refl

------------------------------------------------------------------------------
-- Initiality
⊥ₐ : Asm ℓ
⊥ₐ {ℓ} = (el (Lift ℓ ⊥) hlevel!) , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respects-↠
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isSet       = λ { {_} {()} }
  }
  where
    _⊩_ : Λ₀ → Lift ℓ ⊥ → 𝒰 ℓ
    _ ⊩ ()

    ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
    ⊩-respects-↠ {y = ()}

    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total ()

-- TODO upstream?
strict-initial : {X : 𝒰 ℓ} → (X → Lift ℓ ⊥) → X ≃ (Lift ℓ ⊥)
strict-initial f = f , record { equiv-proof = λ { () } }

module Initial (X : Asm ℓ) where
  universality : Trackable ⊥ₐ X
  universality =  (λ x → absurd (lower x)) , 0 , (λ { {x = ()} })

  strict : (f : Trackable X ⊥ₐ) → AsmIso X ⊥ₐ f
  strict f = ∣ universality , (λ ()) , (λ x → absurd (lower (strict-initial (f .fst) .fst x))) ∣₁

------------------------------------------------------------------------------
-- Product

infixr 5 _×ₐ_
_×ₐ_ : Asm ℓ → Asm ℓ → Asm ℓ
_×ₐ_ {ℓ} X Y = el! (⟨ X ⟩ × ⟨ Y ⟩) , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respect-↠
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isSet       = is-set-β (×-is-of-hlevel 2
    (Σ-is-of-hlevel 2 Λ-is-set λ _ → ×-is-of-hlevel 2 -↠isSet (is-set-η X.⊩-isSet))
    (Σ-is-of-hlevel 2 Λ-is-set λ _ → ×-is-of-hlevel 2 -↠isSet (is-set-η Y.⊩-isSet)))
  }
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

    _⊩_ : Λ₀ → ⟨ X ⟩ × ⟨ Y ⟩ → 𝒰 ℓ
    L ⊩ (x , y) =
      (Σ[ M ꞉ Λ₀ ] ((`projₗ L -↠ M) × (M X.⊩ x))) ×
      (Σ[ N ꞉ Λ₀ ] ((`projᵣ L -↠ N) × (N Y.⊩ y)))

    ⊩-respect-↠   : _⊩_ respects _-↠_ on-the-left
    ⊩-respect-↠ L-↠L′ ((M , proj₁L-↠M , x⊩M) , (N , projᵣL-↠N , y⊩N)) =
      (M , -↠-trans (·ₗ-cong L-↠L′) proj₁L-↠M , x⊩M) ,
      (N , -↠-trans (·ₗ-cong L-↠L′) projᵣL-↠N , y⊩N)

    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total (x , y) = ∥-∥₁.rec²!
      (λ { (M , M⊩x) (N , N⊩y) → ∣ Λ.`⟨ M , N ⟩ , (M , β-projₗ , M⊩x) , N , β-projᵣ , N⊩y ∣₁})
      (X.⊩-right-total x) (Y.⊩-right-total y)

module Product (X Y : Asm ℓ) where
  module X = AsmStr (str X)
  module Y = AsmStr (str Y)

  X×Y = X ×ₐ Y
  module X×Y = AsmStr (str X×Y)


  projₗ : Trackable X×Y X
  projₗ = (λ {(x , y) → x}) , 0 · ↑ 𝑻 , F⊩projₗ
    where
      F⊩projₗ : Tracks X×Y X (0 · (↑ 𝑻)) fst
      F⊩projₗ ((_ , πₗL-↠M , M⫣x) , _) = X.⊩-respects-↠ πₗL-↠M M⫣x

  projᵣ : Trackable X×Y Y
  projᵣ = (λ {(x , y) → y}) , 0 · ↑ 𝑭 , F⊩projᵣ
    where
      F⊩projᵣ : Tracks X×Y Y (0 · ↑ 𝑭) snd
      F⊩projᵣ (_ , _ , π₂L-↠N , N⫣y) = Y.⊩-respects-↠ π₂L-↠N N⫣y

  `⟨_,_⟩ : {Z : Asm ℓ}
    → Trackable Z X → Trackable Z Y → Trackable Z (X ×ₐ Y)
  `⟨_,_⟩ {Z = Z} (f , F , F⊩f) (g , G , G⊩g) = h , H , H⊩h
    where
      module Z   = AsmStr (str Z)
      open -↠-Reasoning

      h : _ → ⟨ X×Y ⟩
      h z = f z , g z

      H = Λ.`⟨ F , G ⟩

      H⊩h : Tracks Z (X ×ₐ Y) H h
      H⊩h {M = L} {x = z} L⊩z = (F [ L ]ₗ , lem₁ , F⊩f L⊩z) , G [ L ]ₗ , lem₂ , G⊩g L⊩z
        where
          lem₁ = begin
            `projₗ (H [ L ]ₗ)
              ≡⟨ refl ⟩
            (ƛ 0 · ↑ F ⟪ exts (subst-zero L) ⟫ · ↑ G ⟪ exts (subst-zero L) ⟫) · 𝑻
              ≡⟨ ap² (λ M N → (ƛ 0 · M · N) · 𝑻) (rename-exts (subst-zero L) F) (rename-exts (subst-zero L) G) ⟩
            (ƛ 0 · ↑ (F [ L ]ₗ) · ↑ (G [ L ]ₗ)) · 𝑻
              -↠⟨ β-projₗ ⟩
            F [ L ]ₗ ∎ₗ

          lem₂ = begin
            `projᵣ (H [ L ]ₗ)
              ≡⟨ refl ⟩
            (ƛ 0 · ↑ F ⟪ exts (subst-zero L) ⟫ · ↑ G ⟪ exts (subst-zero L) ⟫) · 𝑭
              ≡⟨ ap² (λ M N → (ƛ 0 · M · N) · 𝑭) (rename-exts (subst-zero L) F) (rename-exts (subst-zero L) G) ⟩
            (ƛ 0 · ↑ (F [ L ]ₗ) · ↑ (G [ L ]ₗ)) · 𝑭
              -↠⟨ β-projᵣ ⟩
            G [ L ]ₗ ∎ₗ
------------------------------------------------------------------------------
-- Exponential object
infixr 15 _⇒_

_⇒_ : Asm ℓ → Asm ℓ → Asm ℓ
_⇒_ {ℓ} X Y = (el X⇒Y X⇒YisProp) , _⊩_ , record
  { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respects-↠ {x} {x′} {y}
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isSet       = λ {F} {f} → is-set-β (⊩isSet {F} {f})
  }
    where
      open -↠-Reasoning
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

      X⇒Y = MerelyTrackable X Y
      X⇒YisProp = hlevel!

      _⊩_ : Λ₀ → X⇒Y → 𝒰 ℓ
      F ⊩ (f , _) = {M : Λ₀} {x : ⟨ X ⟩} → M X.⊩ x → (F · M Y.⊩ f x)

      ⊩isSet : {F : Λ₀} {f : X⇒Y} → is-set (F ⊩ f)
      ⊩isSet = Π-is-of-hlevel-implicit 2 λ _ →
               Π-is-of-hlevel-implicit 2 λ _ →
               fun-is-of-hlevel 2 (is-set-η Y.⊩-isSet)

      ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respects-↠ {x = G} {x′ = F} G-↠F F⊩f M⊩x = Y.⊩-respects-↠ (·ₗ-cong G-↠F) (F⊩f M⊩x)

      ⊩-right-total : _⊩_ IsRightTotal
      ⊩-right-total (f , ∃F⊩f) = ∥-∥₁.rec!
        (λ { (F , F⊩f) → ∣ ƛ F , (λ {M} M⊩x → Y.⊩-respects-↠
          ((ƛ F) · M -→⟨ β ⟩ F [ M ]ₗ ∎ₗ) (F⊩f M⊩x)) ∣₁})
        ∃F⊩f

module Exponential (X Y : Asm ℓ) where
  module X = AsmStr (str X)
  module Y = AsmStr (str Y)
  X⇒Y = X ⇒ Y
  module X⇒Y = AsmStr (str X⇒Y)

  lem : (M N : Λ₀) → (↑ ↑ M) ⟪ exts (subst-zero N) ⟫ ＝ (↑ M)
  lem M N =
    (↑ ↑ M) ⟪ exts (subst-zero N) ⟫
      ＝⟨ rename-exts (subst-zero N) (↑ M) ⟩
    ↑ (↑ M [ N ]ₗ)
      ＝⟨ ap ↑_ (subst-rename-∅ (subst-zero N) M) ⟩
    ↑ M ∎
--    where open ≡-Reasoning

  pair : ∀ {n} → Λ (suc n) → Λ (suc n) → Subst 1 (suc n)
  pair M N fzero = Λ.`⟨ M , N ⟩

  eval : Trackable (X⇒Y ×ₐ X) Y
  eval = (λ where ((f , _) , x) → f x) , 0 · ↑ 𝑻 · (0 · ↑ 𝑭)  , λ where
    ((_ , red₁ , r₁) , (_ , red₂ , r₂)) → Y.⊩-respects-↠ (·-cong red₁ red₂) (r₁ r₂)

  curry : {Z : Asm ℓ} → Trackable (Z ×ₐ X) Y → Trackable Z X⇒Y
  curry {Z = Z} (f , F , 𝔣) =
    (λ z →
      (λ x → f (z , x)) , ∥-∥₁.rec! (λ { (L , t) → ∣ F ⟪ pair (↑ L) 0 ⟫ ,
        (λ {M} {x} r → Y.⊩-respects-↠
          (begin
            F ⟪ pair (↑ L) 0 ⟫ [ M ]ₗ
              ≡⟨ subst-assoc _ (subst-zero M) F ⟩
            F ⟪ pair (↑ L) 0 ⨟ subst-zero M ⟫
              ≡⟨ subst-cong (λ { fzero → (ap (λ T → ƛ 0 · T · ↑ M) (lem L M)) }) F ⟩
            F [ Λ.`⟨ L , M ⟩ ]ₗ
            ∎ₗ)

          (𝔣 ((_ , β-projₗ , t) , _ , β-projᵣ , r))) ∣₁ })
      (Z.⊩-right-total z)) ,
    ƛ F ⟪ pair 1 0 ⟫ ,
    λ {R} {z} t {M} {x} r → Y.⊩-respects-↠ (begin
      (ƛ F ⟪ pair 1 0 ⟫) [ R ]ₗ · M
        -→⟨ β ⟩
      F ⟪ pair 1 0 ⟫ ⟪ exts (subst-zero R) ⟫ [ M ]ₗ
        ≡⟨ subst-assoc (exts (subst-zero R)) (subst-zero M) (F ⟪ pair 1 0 ⟫) ⟩
      F ⟪ pair 1 0 ⟫ ⟪ exts (subst-zero R) ⨟ subst-zero M ⟫
        ≡⟨ subst-assoc _ _ F ⟩
      F ⟪ pair 1 0 ⨟ (λ x → exts (subst-zero R) x [ M ]ₗ) ⟫
        ≡⟨ subst-cong (λ { fzero → ap (λ T → ƛ 0 · ↑₁ T · ↑₁ M) (subst-rename-∅ (subst-zero M) _)}) F ⟩
      F [ Λ.`⟨ R , M ⟩ ]ₗ ∎ₗ)
      (𝔣 ((_ , β-projₗ , t) , _ , β-projᵣ , r))
    where
      open -↠-Reasoning
      module Z = AsmStr (str Z)
