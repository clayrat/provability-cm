module Assembly.S4 where

open import Prelude
  hiding (id; _∘_)
open import Data.Empty
open import Data.Fin

open import Calculus.Untyped

open import Assembly.Base
open import Assembly.Properties
open import Assembly.Exposure

private
  variable
    ℓ : Level
    X Y Z : Asm ℓ

module _ (Q : Quoting) where
  open Quoting Q

  ⊠_ : Asm ℓ → Asm ℓ
  ⊠_ {ℓ} X@((el |X| XisSet) , _⊩_ , _) = (el |⊠X| isSet⊠X) , _⊩⊠X_ , record
    { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩⊠X-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩⊠X-right-total
    ; ⊩-isSet       = is-set-β (Lift-is-of-hlevel 2 -↠isSet)
    }
    where
      module X = AsmStr (str X)
      |⊠X| : 𝒰 ℓ
      |⊠X| = Σ[ M ꞉ Λ₀ ] (Σ[ x ꞉ |X| ] M ⊩ x)

      isSet⊠X : is-set |⊠X|
      isSet⊠X = Σ-is-of-hlevel 2 Λ-is-set (λ M → Σ-is-of-hlevel 2 XisSet (λ _ → is-set-η X.⊩-isSet))

      _⊩⊠X_ : (M : Λ₀) → |⊠X| → 𝒰 ℓ
      n̅ ⊩⊠X (M , _) = Lift ℓ (n̅ -↠ ⌜ M ⌝ₗ)

      ⊩⊠X-respect-↠ : _⊩⊠X_ respects _-↠_ on-the-left
      ⊩⊠X-respect-↠ M-↠N N-↠⌜L⌝ = lift (-↠-trans M-↠N (lower N-↠⌜L⌝))

      ⊩⊠X-right-total :  _⊩⊠X_ IsRightTotal
      ⊩⊠X-right-total (M , _)  = ∣ ⌜ M ⌝ₗ , lift (⌜ M ⌝ₗ _-↠_.∎ₗ) ∣₁

  ⊠map₀ : {X Y : Asm ℓ} → Trackable X Y → ⟨ ⊠ X ⟩ → ⟨ ⊠ Y ⟩
  ⊠map₀ (f , F , F⊩f) (M , x , M⊩x) = F [ M ]ₗ , f x , F⊩f M⊩x

  ⊠map₁ : Λ₁ → Λ₁
  ⊠map₁ F = (↑ Sub) · (↑ ⌜ F ⌝ₗ) · 0

  ⊠map : {X Y : Asm ℓ} → Trackable X Y → Trackable (⊠ X) (⊠ Y)
  ⊠map {ℓ} {X} {Y} Ff@(f , F , _) = ⊠map₀ Ff , ⊠map₁ F ,
    λ {M} {x} → ⊠F⊩⊠f {M} {x}
    where
      open -↠-Reasoning
      ⊠F⊩⊠f : Tracks (⊠ X) (⊠ Y) (⊠map₁ F) (⊠map₀ Ff)
      ⊠F⊩⊠f {M = n̅} {x = M , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑ Sub [ n̅ ]ₗ · ↑ ⌜ F ⌝ₗ [ n̅ ]ₗ · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = fsuc} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = fsuc} (subst-zero n̅) ⌜ F ⌝ₗ i · n̅ ⟩
        Sub · ⌜ F ⌝ₗ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ₗ · ⌜ M ⌝ₗ
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ]ₗ ⌝ₗ ∎ₗ)

  ⊠id=id : (X : Asm ℓ) → (x : ⟨ ⊠ X ⟩) → ⊠map₀ (id X) x ＝ x
  ⊠id=id X Mxr = refl

  ⊠gf=⊠g⊠f : {X Y Z : Asm ℓ} (f : Trackable X Y) (g : Trackable Y Z)
    → (x : ⟨ ⊠ X ⟩) → ⊠map₀ (g ∘ f) x ＝ ⊠map₀ g ( ⊠map₀ f x)
  ⊠gf=⊠g⊠f {ℓ} {Z = Z} (f , F , F⊩f) (g , G , G⊩g) (M , x , r) i =
    G[F[M]]=G[F][M] i , g (f x) , transport-filler (ap (Z._⊩ g (f x)) (sym G[F[M]]=G[F][M])) (G⊩g (F⊩f r)) (~ i)
    where
      module Z = AsmStr (str Z)
      G[F[M]]=G[F][M] = ∘-ssubst-ssubst G F M

  ⊠reflects∼ : {X Y : Asm ℓ} (f g : Trackable X Y)
    → ⊠map f ∼ ⊠map g -- ∶ ⊠ X →ₐ ⊠ Y
    → f ∼ g -- ∶ X →ₐ Y
  ⊠reflects∼ {ℓ} {X} {Y} f g ⊠f=⊠g x = ∥-∥₁.rec!
    (λ { (M , M⊩x) → ap (λ x → fst (snd x)) (⊠f=⊠g (M , x , M⊩x))  })
    (X.⊩-right-total x)
    where
      module X = AsmStr (str X)

  ⊠-isExposure : IsExposure ℓ ⊠_  ⊠map
  ⊠-isExposure = record
    { preserve-id   = ⊠id=id
    ; preserve-comp = ⊠gf=⊠g⊠f
    ; reflects-∼    = ⊠reflects∼
    }

  ⊠-exposure : Exposure ℓ
  ⊠-exposure = exposure ⊠_ ⊠map ⊠-isExposure

  ⊠F=⊠G→F=G : (F G : Λ₁) → ⊠map₁ F ＝ ⊠map₁ G → F ＝ G
  ⊠F=⊠G→F=G F G ⊠F=⊠G = ⌜⌝-injective (↑ₗ-injective (decodeΛ (encodeΛ ⊠F=⊠G .fst .snd)))
    where
      postulate ↑ₗ-injective : ∀ {m n} {M N : Λ n} → ↑_ {n} {m} M ＝ ↑ N → M ＝ N

  ≤⊠ : (X : Asm ℓ)
    → (x y : ⟨ ⊠ X ⟩) → 𝒰 ℓ
  ≤⊠ X (M , x , r) (N , y , s) = (M -↠ N) × (x ＝ y)

  syntax ≤⊠ X x y = x ≤ y ∶⊠ X

------------------------------------------------------------------------------
-- Global element ★ of ⊠ ⊤

  ★ : Trackable (⊤ₐ {ℓ}) (⊠ ⊤ₐ)
  ★ = Final.global-element ⌜ 𝑰 ⌝ₗ (𝑰 , lift tt , lift -↠-refl) (lift -↠-refl)

------------------------------------------------------------------------------
-- Projections

  ⊠X×Y→⊠X : {X Y : Asm ℓ} → Trackable (⊠ (X ×ₐ Y)) (⊠ X)
  ⊠X×Y→⊠X {ℓ} {X} {Y} = (λ { (L , (x , _) , ((M , red , r) , _)) → ( (ƛ 0 · ↑ 𝑻) · L , x , X.⊩-respects-↠ (begin
    (ƛ 0 · ↑ 𝑻) · L
      -→⟨ β ⟩
    L · ↑ 𝑻 [ L ]ₗ
      -↠⟨ red ⟩
    M ∎ₗ) r) }) ,
    ↑ Ap · ↑ ⌜ ƛ 0 · ↑ 𝑻 ⌝ₗ · 0   , (λ { {M}  {L , _} r → lift (begin
    ↑ Ap [ M ]ₗ · ↑ ⌜ ƛ 0 · ↑ 𝑻  ⌝ₗ [ M ]ₗ · M
      ≡⟨ ap² (λ L N → L · N · M) (subst-rename-∅ _ Ap) (subst-rename-∅ _ ⌜ ƛ 0 · ↑ 𝑻 ⌝ₗ) ⟩
    Ap · ⌜ ƛ 0 · ↑ 𝑻 ⌝ₗ · M
      -↠⟨ ·ᵣ-cong (lower r) ⟩
    Ap · ⌜ ƛ 0 · ↑ 𝑻 ⌝ₗ · ⌜ _ ⌝ₗ
      -↠⟨ Ap-↠ ⟩
    ⌜ (ƛ 0 · ↑ 𝑻) · L ⌝ₗ
      ∎ₗ )})
    where
      open -↠-Reasoning
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

  ⊠X×Y→⊠Y : {X Y : Asm ℓ} → Trackable (⊠ (X ×ₐ Y)) (⊠ Y)
  ⊠X×Y→⊠Y {ℓ} {X} {Y} = (λ { (L , (_ , y) , (_ , (N , red , s))) → ( (ƛ 0 · ↑ 𝑭) · L , y , Y.⊩-respects-↠ (begin
    (ƛ 0 · ↑ 𝑭) · L -→⟨ β ⟩ L · ↑ 𝑭 [ L ]ₗ -↠⟨ red ⟩ N ∎ₗ) s) }) ,
    ↑ Ap · ↑ ⌜ ƛ 0 · ↑ 𝑭 ⌝ₗ · 0   , (λ { {M}  {L , _} r → lift (begin
    ↑ Ap [ M ]ₗ · ↑ ⌜ ƛ 0 · ↑ 𝑭 ⌝ₗ [ M ]ₗ · M
      ≡⟨ ap² (λ L N → L · N · M) (subst-rename-∅ _ Ap) (subst-rename-∅ _ ⌜ ƛ 0 · ↑ 𝑭 ⌝ₗ) ⟩
    Ap · ⌜ ƛ 0 · ↑ 𝑭 ⌝ₗ · M
      -↠⟨ ·ᵣ-cong (lower r) ⟩
    Ap · ⌜ ƛ 0 · ↑ 𝑭 ⌝ₗ · ⌜ _ ⌝ₗ
      -↠⟨ Ap-↠ ⟩
    ⌜ (ƛ 0 · ↑ 𝑭) · L ⌝ₗ
      ∎ₗ )})
    where
      open -↠-Reasoning
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)
------------------------------------------------------------------------
-- Axiom K

  |K| : ⟨ ⊠ (X ⇒ Y) ⟩ → ⟨ ⊠ X ⇒ ⊠ Y ⟩
  |K| {X = X} {Y = Y} (ƛF , (f , _) , 𝔣) = f· , f·-trackable
    where
      open -↠-Reasoning
      f· : ⟨ ⊠ X ⟩ → ⟨ ⊠ Y ⟩
      f· (M , x , r) = (ƛF) · M , f x , 𝔣 r
      f·-trackable : ∥ HasTracker (⊠ X) (⊠ Y) f· ∥₁
      f·-trackable =
        ∣ App ⟪ exts (subst-zero ⌜ ƛF ⌝ₗ) ⟫ , (λ { {M = N} {x = M , x , r} s → lift (begin
          App ⟪ exts (subst-zero ⌜ ƛF ⌝ₗ) ⟫ [ N ]ₗ
            -↠⟨ reduce-ssubst (App ⟪ exts (subst-zero ⌜ ƛF ⌝ₗ) ⟫) (lower s) ⟩
          App ⟪ exts (subst-zero ⌜ ƛF ⌝ₗ) ⟫ [ ⌜ M ⌝ₗ ]ₗ
            -↠⟨ App-↠ ⟩
          ⌜ (ƛF) · M ⌝ₗ
            ∎ₗ)} ) ∣₁

  K : (X Y : Asm ℓ) → Trackable (⊠ (X ⇒ Y)) (⊠ X ⇒ ⊠ Y)
  K X Y = |K| , ƛ App , λ { {M = H} {x = G , _} (lift H↠⌜G⌝) {M = N} {x = M , _} (lift t) → lift (begin
    (ƛ App ⟪ exts (subst-zero H) ⟫) · N
      -↠⟨ ·ᵣ-cong t ⟩
    (ƛ App ⟪ exts (subst-zero H) ⟫) · ⌜ M ⌝ₗ
      -↠⟨ ·ₗ-cong (ƛ-cong (reduce-subst App (extsσ-↠σ′ λ { fzero → H↠⌜G⌝ }))) ⟩
    (ƛ App ⟪ exts (subst-zero ⌜ G ⌝ₗ) ⟫) · ⌜ M ⌝ₗ
      -→⟨ β ⟩
    App ⟪ exts (subst-zero ⌜ G ⌝ₗ) ⟫ [ ⌜ M ⌝ₗ ]ₗ
      -↠⟨ App-↠ ⟩
    ⌜ G · M ⌝ₗ ∎ₗ )}
    where
      open -↠-Reasoning

------------------------------------------------------------------------
-- Axiom T

  eval : (X : Asm ℓ) → Trackable (⊠ X) X
  eval X  = (λ x → fst (snd x)) , Eval ,
    λ { {_} {_ , _ , M⊩x} N-↠⌜M⌝ →
      X.⊩-respects-↠ (reduce-ssubst Eval (lower N-↠⌜M⌝)) ((X.⊩-respects-↠ Eval-↠ M⊩x)) }
    where
      module X  = AsmStr (str X)
      module ⊠X = AsmStr (str (⊠ X))

  eval-nat : {ℓ : Level} → NaturalTransformation ℓ ⊠-exposure Id
  eval-nat = eval , λ _ _ f x → refl

------------------------------------------------------------------------
-- Axiom 4

  quoting : (X : Asm ℓ) → Trackable (⊠ X) (⊠ ⊠ X)
  quoting X = (λ { y@(M , x , r) → ⌜ M ⌝ₗ , y , lift -↠-refl }) , Quote , λ where
    {M = N} {x = M , x , r} (lift N-↠⌜M⌝) → lift (begin
      Quote [ N ]ₗ
        -↠⟨ reduce-ssubst Quote N-↠⌜M⌝ ⟩
      Quote [ ⌜ M ⌝ₗ ]ₗ
        -↠⟨ Quote-↠ ⟩
      ⌜ ⌜ M ⌝ₗ ⌝ₗ ∎ₗ)
      where
        open -↠-Reasoning
        module ⊠X  = AsmStr (str (⊠ X))
        module ⊠⊠X = AsmStr (str (⊠ ⊠ X))

  reasonable-quoting : {X : Asm ℓ} → (a : Trackable ⊤ₐ (⊠ X))
    → ⊠map₀ a (★ .fst (lift tt)) ≤ quoting X .fst (a .fst (lift tt)) ∶⊠ (⊠ X)
  reasonable-quoting (f , F , 𝔣) = lower (𝔣 (lift -↠-refl)) , refl

------------------------------------------------------------------------
-- Refuting X -→ ⊠ X
--  ⊤ ­­­­→ ⊠ ⊤
--  ∣        ∣
--  ∣ a      ∣ ⊠ a
--  ↓        ↓
--  Λ ­­­­→ ⊠ Λ
--
-- quote (a) ≠ ⌜ a ⌝

  no-quoting : (η : Trackable Λ₀ₐ (⊠ Λ₀ₐ))
    → ((M : Λ₀) → η .fst M ＝ ⊠map₀ (Final.global-element {0ℓ} {Λ₀ₐ} M M -↠-refl) (★ .fst (lift tt)))
    → ⊥
  no-quoting η hyp = quoting′-not-definable
    (Qη , Qη-is-quoting)
    where
      open -↠-Reasoning
      Qη = η .snd .HasTracker.F
      Qη-is-quoting : (M : Λ₀) → Qη [ M ]ₗ -↠ ⌜ M ⌝ₗ
      Qη-is-quoting M = begin
        Qη [ M ]ₗ
          -↠⟨ (η .snd .HasTracker.F⊩f) -↠-refl .lower ⟩
        ⌜ η .fst M .fst ⌝ₗ
        ≡⟨ ap ⌜_⌝ₗ (ap fst (hyp M)) ⟩
        ⌜ ↑ M [ _ ]ₗ ⌝ₗ
          ≡⟨ ap ⌜_⌝ₗ (subst-rename-∅ _ M) ⟩
        ⌜ M ⌝ₗ ∎ₗ

------------------------------------------------------------------------
-- Projecting the intension of ⊠ X into ⊠ Λ

  forgetful : {X : Asm 0ℓ} → Trackable (⊠ X) (⊠ Λ₀ₐ)
  forgetful = (λ { (M , _) → M , M , -↠-refl }) , (0 , λ N-↠⌜M⌝ → N-↠⌜M⌝)

  Λ-map : {X Y : Asm 0ℓ} → Trackable X Y → Trackable (⊠ Λ₀ₐ) (⊠ Λ₀ₐ)
  Λ-map (f , F , _) = (λ { (M , N , r) → F [ M ]ₗ , F [ N ]ₗ , reduce-ssubst F r }) ,
    ↑ Sub · (↑ ⌜ F ⌝ₗ) · 0 , λ { {M} {N , _} (lift M-↠N) → lift (begin
      (↑ Sub · (↑ ⌜ F ⌝ₗ) · 0) [ M ]ₗ
        ≡⟨ refl ⟩
      (↑ Sub) [ M ]ₗ · (↑ ⌜ F ⌝ₗ) [ M ]ₗ · M
        ≡⟨ ap² (λ L N → L · N · M) (subst-rename-∅ _ Sub) (subst-rename-∅ _ ⌜ F ⌝ₗ) ⟩
      Sub · ⌜ F ⌝ₗ · M
        -↠⟨ ·ᵣ-cong M-↠N ⟩
      Sub · ⌜ F ⌝ₗ · ⌜ N ⌝ₗ
        -↠⟨ Sub-↠ ⟩
      ⌜ F [ N ]ₗ ⌝ₗ ∎ₗ) }
      where
        open -↠-Reasoning

