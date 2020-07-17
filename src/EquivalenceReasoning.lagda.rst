::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import HomotopyLemmas

   open import HalfAdjointType
   open import QuasiinverseType
   open import QuasiinverseLemmas

Equivalence reasoning
---------------------

::

   module EquivalenceReasoning where

::

     _≃⟨⟩_
       : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) {B : Type ℓ₂}
       → A ≃ B
       -------
       → A ≃ B

     _ ≃⟨⟩ e = e
     infixr 2 _≃⟨⟩_

::

     _≃⟨by-def⟩_
       : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) {B : Type ℓ₂}
       → A ≃ B
       -------
       → A ≃ B

     _ ≃⟨by-def⟩ e = e
     infixr 2 _≃⟨by-def⟩_

::

     _≃⟨_⟩_
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} (A : Type ℓ₁){B : Type ℓ₂} {C : Type ℓ₃}
       → A ≃ B → B ≃ C
       ---------------
       → A ≃ C

     _ ≃⟨ e₁ ⟩ e₂ = ≃-trans e₁ e₂

     infixr 2 _≃⟨_⟩_

::

     _≃∎
       : ∀ {ℓ : Level} (A : Type ℓ)
       → A ≃ A

     _≃∎ = λ A → idEqv {A = A}
     infix  3 _≃∎

::

     begin≃_
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → A ≃ B
       -------
       → A ≃ B

     begin≃_ e = e
     infix  1 begin≃_

::

     move-right-from-composition
      : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
      → (f : A → B) → (e : B ≃ C) → (g : A → C)
      → f :> (e ∙→) ≡ g
      --------------------------------------
      →           f ≡ g :> (e ∙←)

     move-right-from-composition f e .(λ x → π₁ e (f x)) idp =
       begin
        f
          ≡⟨⟩
        f :> id
          ≡⟨ ap (λ w → f :> w) (funext (λ x → ! (rlmap-inverse-h e x))) ⟩
        f :> ((e ∙→) :> (e ∙←))
          ≡⟨ :>-lassoc f (e ∙→) (e ∙←) ⟩
        (f :> (e ∙→)) :> (e ∙←)
        ∎ where open import FunExtAxiom

     move-left-from-composition
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (f : A → B) → (e : B ≃ C) → (g : A → C)
        →           f ≡ g :> (e ∙←)
        --------------------------------------
        → f :> (e ∙→) ≡ g

     move-left-from-composition .(λ x → π₁ (π₁ (π₂ e (g x)))) e g idp
        = :>-rassoc g (e ∙←) (e ∙→)
          · ap (λ w → g :> w) (funext (λ x → lrmap-inverse-h e x))
        where open import FunExtAxiom

     2-out-of-3-property
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (f : A → C) → (e : A ≃ B) → (g : B ≃ C)
        → f ≡ (e ∙→) :> (g ∙→)
        -------------------------
        → isEquiv f

     2-out-of-3-property .(λ x → π₁ g (π₁ e x)) e g idp = comp-is-equiv
        where
        comp-is-equiv : isEquiv ((e ∙→) :> (g ∙→))
        comp-is-equiv = π₂ (≃-trans e g)

     inv-of-equiv-composition
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (f : A ≃ B)
        → (g : B ≃ C)
        → remap ((f ∙→) :> (g ∙→) ,  π₂ (≃-trans f g))
          ≡ (g ∙←) :> (f ∙←)
     inv-of-equiv-composition f g = idp