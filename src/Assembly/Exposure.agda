module Assembly.Exposure where

open import Prelude
  hiding (id; _∘_)
open import Calculus.Untyped

open import Assembly.Base
open import Assembly.Properties

------------------------------------------------------------------------------
-- Endo-exposure

record IsExposure (ℓ : Level) (Q : Asm ℓ → Asm ℓ) (map : {X Y : Asm ℓ} → Trackable X Y → Trackable (Q X) (Q Y)) : 𝒰 (ℓsuc ℓ) where
  field
    preserve-id   : (X : Asm ℓ)
      → map (id X) ∼ id (Q X) -- ∶ Q X →ₐ Q X
    preserve-comp : {X Y Z : Asm ℓ} (f : Trackable X Y) (g : Trackable Y Z)
      → map (g ∘ f) ∼ map g ∘ map f -- ∶ Q X →ₐ Q Z
    reflects-∼    : {X Y : Asm ℓ} (f g : Trackable X Y)
      → map f ∼ map g -- ∶ Q X →ₐ Q Y
      →     f ∼ g -- ∶ X →ₐ Y

record Exposure (ℓ : Level) : 𝒰 (ℓsuc ℓ) where
  constructor exposure
  field
    obj        : Asm ℓ → Asm ℓ
    map        : {X Y : Asm ℓ} → Trackable X Y → Trackable (obj X) (obj Y)
    isExposure : IsExposure ℓ obj map
open Exposure

record NaturalTransformation (ℓ : Level) (P Q : Exposure ℓ) : 𝒰 (ℓsuc ℓ) where
  constructor _,_
  field
    fun        : (X : Asm ℓ) → Trackable (P .obj X) (Q .obj X)
    naturality : (X Y : Asm ℓ) → (f : Trackable X Y)
      → ∼-eq (P .obj X) (Q . obj Y) ((fun Y) ∘ P .map f) (Q .map f ∘ (fun X))

Id : {ℓ : Level} → Exposure ℓ
Id = exposure (λ X → X) (λ f → f) record
  { preserve-id   = λ _ x   → refl
  ; preserve-comp = λ f g x → refl
  ; reflects-∼    = λ _ _ x → x
  }
