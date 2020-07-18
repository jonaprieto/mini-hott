
module Tests where
  open import BasicFunctions
  open import TransportLemmas
  open import EquivalenceType
  open import QuasiinverseType
  open import QuasiinverseLemmas
  open import HLevelLemmas
  open import UnivalenceAxiom

  equiv-is-inj
    : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
    → (f : A → B) → isEquiv f
    → ∀ {x y : A} → (f x ≡ f y) → x ≡ y
  equiv-is-inj {A = A}{B} f f-is-equiv fx≡fy = ! cr · (ap f^-1 fx≡fy · cr)
    where
    f^-1 : B → A
    f^-1 = remap (f , f-is-equiv)

    cr : ∀ {x : A} → f^-1 (f x) ≡ x
    cr = rlmap-inverse (f , f-is-equiv)

  module _ {ℓ : Level} {A : Type ℓ} where
    equiv-induction
        : (P : (C : Type ℓ) → (A ≃ C) → Type ℓ)
        → P A idEqv
        → (C : Type ℓ)
        → (e : A ≃ C)
        -----------------------------
        → P C e

    equiv-induction P p-refl C e  = tr (P C) (ua-β e) g
      where
      P' :  (C : Type ℓ) → A ≡ C → Type ℓ
      P' C p = P C (idtoeqv p)

      b' : P A (idtoeqv idp)
      b' = tr (P A) (sameEqv idp) p-refl

      f' : (C : Type ℓ) → (p : A ≡ C) → P C (idtoeqv p)
      f' C idp = b'

      g : P C (idtoeqv (ua e))
      g = f' C (ua e)

    postcomp-is-equiv
      : (B : Type ℓ)
      → (e : A ≃ B)
      → ∀ {C : Type ℓ}
      → isEquiv {A = C → A} {B = C → B} (_:> (e ∙→))

    postcomp-is-equiv  B e
      = equiv-induction (λ C A≃C → isEquiv (_:> (A≃C ∙→) )) base-case B e
      where
      base-case : isEquiv (λ f x → π₁ idEqv (f x))
      base-case = π₂ idEqv


    postcomp-≃
      : (B : Type ℓ)
      → (e : A ≃ B)
      → (C : Type ℓ)
      → (C → A) ≃ (C → B)
    postcomp-≃ B e C  = (_:> (e ∙→)) , postcomp-is-equiv B e

    postcomp-is-inj
      : (B : Type ℓ)
      → (e : A ≃ B)
      → {C : Type ℓ}
      → (f g : C → A)
      → f :> (e ∙→) ≡ g :> (e ∙→)
      → f ≡ g

    postcomp-is-inj B e f g p =
      equiv-is-inj (_:> (e ∙→)) (postcomp-is-equiv B e) p

  --  The naive non-dependent function extensionality axiom
  funext'
    : {ℓ : Level} {A : Type ℓ}{B : Type ℓ}
    → (f g : A → B)
    → (h : ∏[ x ∶ A ] (f x ≡ g x))
    → f ≡ g

  funext' {A = A}{B} f g h = ap (_:> p₁) d≡e
    where
    d e : A → ∑[ (x , y ) ∶ (B × B) ] (x ≡ y)
    d = λ x → ((f x , f x)) , refl (f x)
    e = λ x → ((f x , g x)) , h x

    p₀ : ∑[ (x , y ) ∶ (B × B) ] (x ≡ y) → B
    p₀ ((x , y) , p) = x

    p₁ : ∑[ (x , y ) ∶ (B × B) ] (x ≡ y) → B
    p₁ ((x , y) , p) = y

    p₀-is-equiv : isEquiv p₀
    p₀-is-equiv
      = π₂ (qinv-≃ p₀ ((λ x → ((x , x) , (refl x) )) ,
          (λ {p → idp}) , (λ {((x , .x) , idp) → idp})))

    d:>p₀≡e:>p₀ : (d :> p₀) ≡ (e :> p₀)
    d:>p₀≡e:>p₀ = idp

    d≡e : d ≡ e
    d≡e = postcomp-is-inj B (p₀ , p₀-is-equiv) d e d:>p₀≡e:>p₀

