Transport with fibers
---------------------


::

   {-# OPTIONS --without-K  --exact-split #-}
   open import BasicTypes
   open import Transport
   open import FibreType

::

   fibre-transport
     : ∀ {ℓ₁ ℓ₂ : Level}{A : Type ℓ₁} {B : Type ℓ₂}
     → (f : A → B)
     → {b b' : B} → (h : b == b')
     ------------------------------------------------
     → ∀ a e → (a , e) == (a , (e · h)) [ (fibre f) ↓ h ]

   fibre-transport f idp a idp = idp
