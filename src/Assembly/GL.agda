{-# OPTIONS --guarded #-}

module Assembly.GL where

open import Prelude
  hiding (id; _∘_)
open import Data.Empty
open import Data.Fin

open import Later

open import Calculus.Untyped

open import Assembly.Base
open import Assembly.Properties
open import Assembly.ClockedExposure

private
  variable
    ℓ : Level
    X Y Z : Asm ℓ
    k     : Cl

module _ (Q : Quoting) where
  open Quoting Q

  □ : (k : Cl) → Asm ℓ → Asm ℓ
  □ {ℓ} k ((el |X| XisSet) , Xstr) = (el |□X| isSet□X) , _⊩_ , record
    { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩-right-total
    ; ⊩-isSet       = is-set-β (Lift-is-of-hlevel 2 -↠isSet)
    }
    where
      module X = AsmStr Xstr
      |□X| : 𝒰 ℓ
      |□X| = Σ[ M ꞉ Λ₀ ] (Σ[ ▹x ꞉ ▹ k |X| ] (▹[ α ∶ k ] M X.⊩ ▹x α))

      isSet□X : is-set |□X|
      isSet□X = Σ-is-of-hlevel 2 Λ-is-set
        (λ _ → Σ-is-of-hlevel 2 (▹isSet→isSet▹ (λ _ → XisSet))
                 (λ _ → ▹isSet→isSet▹ (λ _ → is-set-η X.⊩-isSet)))

      _⊩_ : (M : Λ₀) → |□X| → 𝒰 ℓ
      n̅ ⊩ (M , _)= Lift ℓ (n̅ -↠ ⌜ M ⌝ₗ)

      ⊩-respect-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respect-↠ M-↠N N-↠⌜L⌝ = lift (-↠-trans M-↠N (lower N-↠⌜L⌝))

      ⊩-right-total :  _⊩_ IsRightTotal
      ⊩-right-total (M , _) = ∣ ⌜ M ⌝ₗ , lift -↠-refl ∣₁

  □map₀ : Trackable X Y → ⟨ □ k X ⟩ → ⟨ □ k Y ⟩
  □map₀ (f , F , F⊩f) (M , x , M⊩x) = F [ M ]ₗ , ▹map f x , λ α → F⊩f (M⊩x α)

  □map₁ : Λ₁ → Λ₁
  □map₁ F = ↑ Sub · ↑ ⌜ F ⌝ₗ · 0

  □map : (k : Cl) → Trackable X Y → Trackable (□ k X) (□ k Y)
  □map {X} {Y} _ Ff@(f , F , _) = □map₀ Ff , □map₁ F ,
    λ {M} {x} → □F⊩□f {_} {M} {x}
    where
      open -↠-Reasoning
      □F⊩□f : Tracks (□ k X) (□ k Y) (□map₁ F) (□map₀ Ff)
      □F⊩□f {M = n̅} {x = M , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑ Sub [ n̅ ]ₗ · ↑ ⌜ F ⌝ₗ [ n̅ ]ₗ · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = fsuc} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = fsuc} (subst-zero n̅) ⌜ F ⌝ₗ i · n̅ ⟩
        Sub · ⌜ F ⌝ₗ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ₗ · ⌜ M ⌝ₗ
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ]ₗ ⌝ₗ ∎ₗ)

  □id=id : (X : Asm ℓ) → (x : ⟨ □ k X ⟩) → □map₀ (id X) x ＝ x
  □id=id X Mxr = refl

  □gf=□g□f : {X Y Z : Asm ℓ} (f : Trackable X Y) (g : Trackable Y Z) → (x : ⟨ □ k X ⟩) → □map₀ (g ∘ f) x ＝ □map₀ g (□map₀ f x)
  □gf=□g□f {Z = Z} (f , F , F⊩f) (g , G , G⊩g) (M , x , r) i = G[F[M]]=G[F][M] i , ▹map g (▹map f x) , λ α →
    transport-filler (ap (Z._⊩ (▹map g (▹map f x) α)) (sym G[F[M]]=G[F][M])) (G⊩g (F⊩f (r α))) (~ i)
    where
      module Z = AsmStr (str Z)
      G[F[M]]=G[F][M] = ∘-ssubst-ssubst G F M

  □reflects∼ : {X Y : Asm ℓ} (f g : Trackable X Y)
    → ((k : Cl) → □map k f ∼ □map k g)
    → (k : Cl) → f ∼ g
  □reflects∼ {ℓ} {X} {Y} (f , F , F⊩f) (g , G , G⊩g) □f∼□g k x = ∥-∥₁.rec!
    (λ { (M , r) → ▹x=▹y→x=y  (λ k → ap (λ x → fst (snd x)) (□f∼□g k (M , next x , next r))) k })
    (X.⊩-right-total x)
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

  □-isExposure : IsCloExpo {ℓ} □ □map
  □-isExposure = record
    { preserve-id   = □id=id
    ; preserve-comp = □gf=□g□f
    ; reflects-∼    = □reflects∼
    }

  □F=□G→F=G : (F G : Λ₁) → □map₁ F ＝ □map₁ G → F ＝ G
  □F=□G→F=G F G □F=□G = ⌜⌝-injective (↑ₗ-injective (decodeΛ (encodeΛ □F=□G .fst .snd)))
    where
      postulate
        ↑ₗ-injective : {n m : ℕ} {M N : Λ m} → ↑_ {m} {n} M ＝ ↑ N → M ＝ N

  □-exposure : CloExpo ℓ
  □-exposure = exposure □ □map □-isExposure

  □⊤ : Trackable (⊤ₐ {ℓ}) (□ k ⊤ₐ)
  □⊤ = Final.global-element ⌜ 𝑰 ⌝ₗ (𝑰 , next (lift tt) , next (lift -↠-refl)) (lift -↠-refl)
    where open -↠-Reasoning

  |K| : ⟨ □ k (X ⇒ Y) ⟩ → ⟨ □ k X ⇒ □ k Y ⟩
  |K| (ƛF , f , 𝔣) =
    ( λ{ (M , x , r) → ƛF · M , (λ α → f α .fst (x α)) , λ α → 𝔣 α (r α)})
    , ∣ App ⟪ exts (subst-zero ⌜ ƛF ⌝ₗ) ⟫ , (λ { {M = N} {x = M , _ , _} s → lift (begin
      App ⟪ exts (subst-zero ⌜ ƛF ⌝ₗ) ⟫ [ N ]ₗ
        -↠⟨ reduce-ssubst (App ⟪ exts (subst-zero ⌜ ƛF ⌝ₗ) ⟫) (lower s) ⟩
      App ⟪ exts (subst-zero ⌜ ƛF ⌝ₗ) ⟫ [ ⌜ M ⌝ₗ ]ₗ
        -↠⟨ App-↠ ⟩
      ⌜ (ƛF) · M ⌝ₗ ∎ₗ)} ) ∣₁
    where
      open -↠-Reasoning

  K : (X Y : Asm ℓ) → Trackable (□ k (X ⇒ Y)) (□ k X ⇒ □ k Y)
  K X Y = |K| , ƛ App , λ { {M = H} {x = G , _} (lift H↠⌜G⌝) {M = N} {x = M , _} (lift t)→ lift (begin
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

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ k (⊥ₐ {ℓ}) ⟩ → Lift ℓ ⊥) → ▹ k (Lift ℓ ⊥) → Lift ℓ ⊥
  bang eval⊥ ▹x = eval⊥ (𝑰 , ▹x , λ α → absurd (lower (▹x α)))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {ℓ} (□ k ⊥ₐ) ⊥ₐ → Lift ℓ ⊥
  eval-does-not-exist e = fix (bang (e .fst))

  no-quoting : (η : Trackable Λ₀ₐ (□ k Λ₀ₐ))
    → ((M : Λ₀) → η .fst M ＝ □map₀ (Final.global-element {0ℓ} {Λ₀ₐ} M M -↠-refl) (𝑰 , next (lift tt) , next (lift -↠-refl)))
    → ⊥
  no-quoting η hyp = quoting′-not-definable
    (Qη , Qη-is-quoting)
    where
      open -↠-Reasoning
      Qη = η .snd .HasTracker.F
      Qη-is-quoting : (M : Λ₀) → Qη [ M ]ₗ -↠ ⌜ M ⌝ₗ
      Qη-is-quoting M = begin
        Qη [ M ]ₗ
          -↠⟨ (η .snd .HasTracker.F⊩f) -↠-refl .lower  ⟩
        ⌜ η .fst M .fst ⌝ₗ
        ≡⟨ ap ⌜_⌝ₗ (ap fst (hyp M)) ⟩
        ⌜ ↑ M [ _ ]ₗ ⌝ₗ
          ≡⟨ ap ⌜_⌝ₗ (subst-rename-∅ _ M)  ⟩
        ⌜ M ⌝ₗ ∎ₗ

  @0 _† : Trackable (□ k X) X
     → Trackable ⊤ₐ (□ k X)
  _† {k} {_} {X} (|f| , F , 𝔣) = Final.global-element ⌜ sfix F ⌝ₗ (sfix F , fixf) (lift -↠-refl)
    where
      module X = AsmStr (str X)
      fold : (x : ▹ k ⟨ X ⟩) → ▹[ α ∶ k ] F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x α
           → ▹[ α ∶ k ] sfix F X.⊩ x α
      fold x r α = X.⊩-respects-↠ sfix-↠ (r α)

      h : Σ[ x ꞉ ▹ k ⟨ X ⟩ ] (▹[ α ∶ k ] F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x α)
        → Σ[ x ꞉     ⟨ X ⟩ ]            (F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x)
      h (x , r) = |f| (sfix F , x , fold x r) , 𝔣 (lift -↠-refl)

      fixf : Σ[ x ꞉ ▹ k ⟨ X ⟩ ] (▹[ α ∶ k ] sfix F X.⊩ x α)
      fixf = dfixΣ h .fst , fold (dfixΣ h .fst) (dfixΣ h .snd)

  run : (∀ k → ⟨ □ k X ⟩) → (k′ : Cl) → ⟨ X ⟩
  run {X = X} x k′ = force x′ k′
    where
      x′ : ∀ k → ▹ k ⟨ X ⟩
      x′ k α = x k .snd .fst α

  @0 _‡ : Trackable (□ k X) X
     → Trackable ⊤ₐ X
  _‡ {k} {_} {X} (|f| , F , 𝔣) =
    Final.global-element (sfix F) fixf fixr
    where
      module X = AsmStr (str X)
      fold : (x : ▹ k ⟨ X ⟩) → ▹[ α ∶ k ] F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x α
           → ▹[ α ∶ k ] sfix F X.⊩ x α
      fold x r α = X.⊩-respects-↠ sfix-↠ (r α)

      h : Σ[ x ꞉ ▹ k ⟨ X ⟩ ] (▹[ α ∶ k ] F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x α)
        → Σ[ x ꞉     ⟨ X ⟩ ]           ( F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x)
      h (x , r) = |f| (sfix F , x , fold x r) , 𝔣 (lift -↠-refl)

      fixf : ⟨ X ⟩
      fixf = fixΣ h .fst

      fixr : sfix F X.⊩ fixf
      fixr = X.⊩-respects-↠ sfix-↠ (fixΣ h .snd)

{-
  □′ has a different but equivalent defininition from □.

  The later modality now lives outside the second Σ-type:

      |□X| = Σ[ M ∶ Λ₀ ] ▹ k (Σ[ x ∶ ⟨ X ⟩ ] M X.⊩ x)

  instead of inside the second Σ-type:

      |□X| = Σ[ M ∶ Λ₀ ] Σ[ ▹x ∶ ▹ k |X| ] ▹[ α ∶ k ] M X.⊩ ▹x α
-}
  □′ : (k : Cl) → Asm ℓ → Asm ℓ
  □′ {ℓ} k X = (el |□X| isSet□X) , _⊩_ , record
    { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩-right-total
    ; ⊩-isSet       = is-set-β (Lift-is-of-hlevel 2 -↠isSet)
    }
    where
      module X = AsmStr (str X)
      |□X| : 𝒰 ℓ
      |□X| = Σ[ M ꞉ Λ₀ ] (▹ k (Σ[ x ꞉ ⟨ X ⟩ ] (M X.⊩ x)))

      isSet□X : is-set |□X|
      isSet□X = Σ-is-of-hlevel 2 Λ-is-set (λ _ → ▹isSet→isSet▹ λ _ → Σ-is-of-hlevel 2 hlevel! (λ _ → is-set-η X.⊩-isSet))

      _⊩_ : (M : Λ₀) → |□X| → 𝒰 ℓ
      n̅ ⊩ (M , _)= Lift ℓ (n̅ -↠ ⌜ M ⌝ₗ)

      ⊩-respect-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)

      ⊩-right-total :  _⊩_ IsRightTotal
      ⊩-right-total (M , _) = ∣ ⌜ M ⌝ₗ , lift -↠-refl ∣₁

  □′map₀ : Trackable X Y
    → ⟨ □′ k X ⟩ → ⟨ □′ k Y ⟩
  □′map₀ (|f| , F , F⊩f) (M , x) = F [ M ]ₗ , λ α → |f| (x α .fst) , F⊩f (x α .snd)

  module _ {X : Asm ℓ} where
    module X = AsmStr (str X)

    _†′ : Trackable (□′ k X) X
      →  Trackable ⊤ₐ       (□′ k X)
    _†′ {k} (|f| , F , 𝔣) = Final.global-element ⌜ sfix F ⌝ₗ (sfix F , fixf′) (lift -↠-refl)
      where
        backward : Σ[ x ꞉ ⟨ X ⟩ ] (F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x) → Σ[ x ꞉ ⟨ X ⟩ ] (sfix F X.⊩ x)
        backward (x , r) = x , X.⊩-respects-↠ sfix-↠ r

        h : ▹ k (Σ[ x ꞉ ⟨ X ⟩ ] (F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x))
          →     Σ[ x ꞉ ⟨ X ⟩ ] (F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x)
        h x = |f| (sfix F , ▹map backward x) , 𝔣 (lift -↠-refl)

        fixf′ : ▹ k (Σ[ x ꞉ ⟨ X ⟩ ] (sfix F X.⊩ x))
        fixf′ α = backward (dfix h α)

    _‡′ : Trackable (□′ k X) X
      → Trackable ⊤ₐ X
    _‡′ {k} (|f| , F , 𝔣) =
      Final.global-element (sfix F) (fixf .fst) (fixf .snd)
      where
        backward : Σ[ x ꞉ ⟨ X ⟩ ] (F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x) → Σ[ x ꞉ ⟨ X ⟩ ] (sfix F X.⊩ x)
        backward (x , r) = x , X.⊩-respects-↠ sfix-↠ r

        h : ▹ k (Σ[ x ꞉ ⟨ X ⟩ ] (F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x))
          →     Σ[ x ꞉ ⟨ X ⟩ ] (F [ ⌜ sfix F ⌝ₗ ]ₗ X.⊩ x)
        h x = |f| (sfix F , ▹map backward x) , 𝔣 (lift -↠-refl)

        fixf : Σ[ x ꞉ ⟨ X ⟩ ] (sfix F X.⊩ x)
        fixf = backward (fix h)

        -- fixpoint equation
        -- f ‡ ∼ f ∘ □ᵏ f ‡ ∘ ★

        fixf-path : fixf .fst ＝ |f| (sfix F , next fixf)
        fixf-path =
          backward (fix h) .fst
            ＝⟨ ap (λ x → backward x .fst) (fix-path h) ⟩
          backward (h (next (fix h))) .fst
            ＝⟨⟩
          backward (|f| (sfix F , ▹map backward (next (fix h))) , 𝔣 (lift -↠-refl)) .fst
            ＝⟨⟩
          |f| (sfix F , ▹map backward (next (fix h)))
            ∎
--          where open ≡-Reasoning

    -- Note that the strong Loeb axiom cannot be realised by the SRT, since the intension ƛF is not available
    |IGL| : ⟨ □′ k (□′ k X ⇒ X) ⟩ → ⟨ □′ k X ⟩
    |IGL| {k} f@(ƛF , |f|) = gfix ƛF , λ α → backward (fix h α)
      where
        backward : Σ[ x ꞉ ⟨ X ⟩ ] (ƛF · ⌜ gfix ƛF ⌝ₗ X.⊩ x) → Σ[ x ꞉ ⟨ X ⟩ ] (gfix ƛF X.⊩ x)
        backward (x , r) = x , X.⊩-respects-↠ gfix-↠ r

        h : ▹ k (▹ k (Σ[ x ꞉ ⟨ X ⟩ ] (ƛF · ⌜ gfix ƛF ⌝ₗ X.⊩ x)))
          → ▹ k (Σ[ x ꞉ ⟨ X ⟩ ] (ƛF · ⌜ gfix ƛF ⌝ₗ X.⊩ x))
        h x α = |f| α .fst .fst (gfix ƛF , ▹map backward (x α))
          , |f| α .snd (lift -↠-refl)

    IGL : Trackable (□′ k (□′ k X ⇒ X)) (□′ k X)
    IGL = |IGL| , igfix , λ { {M = G} {x = ƛF , ▹f} (lift r) → lift (begin
      igfix [ G ]ₗ
        -↠⟨ reduce-ssubst igfix r ⟩
      igfix [ ⌜ ƛF ⌝ₗ ]ₗ
        -↠⟨ igfix-↠ ⟩
      ⌜ gfix ƛF ⌝ₗ ∎ₗ)}
       where open -↠-Reasoning
