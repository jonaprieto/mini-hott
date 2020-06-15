::

   {-# OPTIONS --without-K --exact-split #-}
   open import BasicTypes

Fibre type
----------

::

   module
     FibreType {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       where

::

     fibre
       : (f : A → B)
       → (b : B)
       ---------------
       → Type (ℓ₁ ⊔ ℓ₂)

     fibre f b = Σ A (λ a → f a == b)

Synomyms and syntax sugar:

::

     fib   = fibre
     fiber = fibre

     syntax fibre f b = f // b

A function applied over the fiber returns the original point

::

     fib-eq
       : ∀ {f : A → B} {b : B}
       → (h : fib f b)
       ------------------
       → f (proj₁ h) == b

     fib-eq (a , α) = α

Each point is on the fiber of its image.

::

     fib-image
       :  ∀ {f : A → B} → {a : A}
       → fib f (f a)

     fib-image {f} {a} = a , refl (f a)
