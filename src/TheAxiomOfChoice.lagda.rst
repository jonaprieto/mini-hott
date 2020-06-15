::

   {-# OPTIONS --without-K --exact-split #-}
   open import BasicTypes

   open import HLevelTypes
   open import TruncationType

The Axiom Of Choice
~~~~~~~~~~~~~~~~~~~

::

   module
     TheAxiomOfChoice
     where

Let’s write in type theory, the following logic formulation of of the
axiom of choice:

.. math::


     (∀ (b : B) . ∃ (a : A b) . P(b,a))
     ⇒ ∃ (g : (b : B) → A b) . ∀ (b : B) . P (b, g(b)) .

::

     postulate
       Choice
         : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level }
         -- Asummption 1:
           (B : Type ℓ₁)
         → isSet B
         -- Asummption 2:
         → (A : B → Type ℓ₂)
         → ∀ (b : B) → isSet (A b)
         -- Asummption 3:
         → (P : (b : B) → (A b) → Type ℓ₃)
         → ∀ (b : B)(a : A b) → isProp (P b a)
         -----------------------------------
         → (∀ b → ∥ ∑ (A b) (λ a → P b a) ∥)
         → ∥ ∑ (∏ B A) (λ g → P b (g b)) ∥
