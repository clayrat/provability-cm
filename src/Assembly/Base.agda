module Assembly.Base where

open import Prelude
  hiding (_∘_; _∘′_; id)
open import Data.Fin
open import Correspondences.Base
open import Calculus.Untyped

-- TODO make interlude

private variable
  ℓ ℓ′ : Level

_respects_on-the-left : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
  → (_≈_ : A → B → 𝒰 (ℓ ⊔ ℓ′)) → (_∼_ : A → A → 𝒰 ℓ) → 𝒰 (ℓ ⊔ ℓ′)
_respects_on-the-left {A} {B} _≈_ _∼_  = {x x′ : A} {y : B} → x ∼ x′ → x′ ≈ y → x ≈ y

_respects_on-the-right : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
  → (_≈_ : A → B → 𝒰 (ℓ ⊔ ℓ′)) → (_∼_ : B → B → 𝒰 ℓ′) → 𝒰 (ℓ ⊔ ℓ′)
_respects_on-the-right {A} {B} _≈_ _∼_ = {y y′ : B} {x : A} → y ∼ y′ → x ≈ y′ → x ≈ y

_IsRightTotal : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
    → (_≈_ : A → B → 𝒰 (ℓ ⊔ ℓ′)) → 𝒰 (ℓ ⊔ ℓ′)
_IsRightTotal {A} {B} _≈_ = (y : B) → ∃[ x ꞉ A ] (x ≈ y)

_IsLeftTotal : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
    → (_≈_ : A → B → 𝒰 (ℓ ⊔ ℓ′)) → 𝒰 (ℓ ⊔ ℓ′)
_IsLeftTotal {A} {B} _≈_ = (x : A) → ∃[ y ꞉ B ] (x ≈ y)

-- if M ⊩ x, M is a realiser of x
record IsRealisability {X : 𝒰 ℓ} (_⊩_ : Λ₀ → X → 𝒰 ℓ) : 𝒰 ℓ where
  field
    ⊩-respects-↠  : _⊩_ respects _-↠_ on-the-left
    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-isSet       : ∀ {M x} → (a b : M ⊩ x) → (p q : a ＝ b) → p ＝ q
    -- ⊩-isProp     : Π[ M ∶ Λ₀ ] Π[ x ∶ X ] isProp (M ⊩ x)
    -- ⊩-isProp is useful when defining □, but however it does not seem necessary to define ASM?

record AsmStr (X : 𝒰 ℓ) : 𝒰 (ℓsuc ℓ) where
  constructor _,_
  field
    _⊩_           : Λ₀ → X → 𝒰 ℓ
    realisability : IsRealisability _⊩_
  open IsRealisability realisability public
  infix 6 _⊩_

record Asm (ℓ : Level) : 𝒰 (ℓsuc ℓ) where
  constructor _,_
  field
    carrier   : Set ℓ
    structure : AsmStr ⌞ carrier ⌟

⟨_⟩ : Asm ℓ → 𝒰 ℓ
⟨ X ⟩ = ⌞ Asm.carrier X ⌟

str : (X : Asm ℓ) → AsmStr ⟨ X ⟩
str (X , s) = s

Asm₀ : 𝒰 (ℓsuc 0ℓ)
Asm₀ = Asm 0ℓ

private
  variable
    X Y Z : Asm ℓ
------------------------------------------------------------------------------
-- Morphisms between assemblies

Tracks : (X Y : Asm ℓ)
  → Λ₁ → (⟨ X ⟩ → ⟨ Y ⟩) → 𝒰 ℓ
Tracks X Y F f = {M : Λ₀} {x : ⟨ X ⟩}
  →       M X.⊩ x
  → F [ M ]ₗ Y.⊩ f x
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

record HasTracker (X Y : Asm ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝒰 ℓ where
  constructor _,_

  field
    F   : Λ₁
    F⊩f : Tracks X Y F f

--HasTracker : (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
--HasTracker X Y f = Σ[ F ∶ Λ₁ ] Tracks X Y F f

--record Trackable (X Y : Asm 𝓤) : 𝓤 ̇ where
--  constructor _,_
--  field
--    f          : ⟨ X ⟩ → ⟨ Y ⟩
--    hasTracker : HasTracker X Y f

-- aka P-function
Trackable : (X Y : Asm ℓ) → 𝒰 ℓ
Trackable X Y = Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] HasTracker X Y f

MerelyTrackable : (X Y : Asm ℓ) → 𝒰 ℓ
MerelyTrackable X Y = Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥₁

------------------------------------------------------------------------------
-- Extensional equality between morphisms

-- Partial equivalence mere relation
record isPER {X : 𝒰 ℓ} (_∼_ : Corr² ℓ (X , X)) : 𝒰 (ℓsuc ℓ) where
  field
    symmetric  : {x y : X}
      → x ∼ y → y ∼ x
    transitive : {x y z : X}
      → x ∼ y → y ∼ z → x ∼ z
    prop : (x y : X) → (a b : x ∼ y) → a ＝ b

∼-eq : (X Y : Asm ℓ) → (f g : Trackable X Y) → 𝒰 ℓ
∼-eq X Y f g = (x : ⟨ X ⟩) → f .fst x ＝ g .fst x

∼-syntax : {X Y : Asm ℓ} → (f g : Trackable X Y) → 𝒰 ℓ
∼-syntax {X = X} {Y = Y} f g = ∼-eq X Y f g

infix 4 ∼-syntax
syntax ∼-syntax f g = f ∼ g

∼-isProp : (f g : Trackable X Y) → is-prop (∼-eq X Y f g)
∼-isProp {X = X} {Y} (f , _ , _) (g , _ , _) = hlevel!

∼-is-PER : {X Y : Asm ℓ}
  → isPER (∼-eq X Y)
∼-is-PER = record
  { symmetric  = λ { f=g     x → sym (f=g x) }
  ; transitive = λ { f=g g=h x → f=g x ∙ g=h x }
  ; prop       = λ x y → is-prop-β (∼-isProp x y)
  }

id : (X : Asm ℓ) → Trackable X X
id X = Prelude.id , 0 , Prelude.id

infixr 9 _∘_

_∘_ : {X Y Z : Asm ℓ}
  → Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {Z = Z} (g , G , G⊩g) (f , F , F⊩f) = (Prelude._∘_ g f) , (G ∘′ F) , λ {_} {x} M⊩x →
  subst (Z._⊩ g (f x)) (sym $ ∘-ssubst-ssubst G F _) (G⊩g (F⊩f M⊩x))
    where module Z = AsmStr (str Z)

AsmIso : (X Y : Asm ℓ) → (Trackable X Y) → 𝒰 ℓ
AsmIso X Y f = ∃[ g ꞉ Trackable Y X ] (∼-eq Y Y (f ∘ g) (id Y)) × (∼-eq X X (g ∘ f) (id X))
