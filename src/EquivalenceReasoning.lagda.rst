::

   {-# OPTIONS --without-K --exact-split #-}
   -- module _ where

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

     postulate
      move-right-from-composition
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (e1 : A → B) → (e2 : B ≃ C) → (e3 : A → C)
        → e1 :> (e2 ∙) ≡ e3
        --------------------------------------
        →           e1 ≡ e3 :> (e2 ∙←)

      move-left-from-composition
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (e1 : A → B) → (e2 : B ≃ C) → (e3 : A → C)
        →           e1 ≡ e3 :> (e2 ∙←)
        --------------------------------------
        → e1 :> (e2 ∙) ≡ e3

      2-out-of-3-property
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
       → (e1 : A → C) → (e2 : A ≃ B) → (e3 : B ≃ C)
       → e1 ≡ (e2 ∙) :> (e3 ∙)
       -------------------------
       → isEquiv e1

      inv-of-equiv-composition
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (f : A ≃ B)
        → (g : B ≃ C)
        → remap ((f ∙→) :> (g ∙→) ,  π₂ (≃-trans f g)) ≡ (g ∙←) :> (f ∙←)
