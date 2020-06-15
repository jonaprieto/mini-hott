Dependent function extensionality transport case
------------------------------------------------

::

   {-# OPTIONS --without-K --exact-split #-}
   module _ where
   open import Transport
   open import TransportLemmas

   open import CoproductIdentities

   open import EquivalenceType
   open import FunExtAxiom
   open import FunExtTransport
   open import QuasiinverseLemmas

::

   module
     FunExtTransportDependent
     {ℓ₁ ℓ₂ : Level}{X : Type ℓ₁} {A : X → Type ℓ₂}{B : (x : X) → A x → Type ℓ₂}{x y : X}
     where

::

     funext-transport-dfun
       : (p : x == y)
       → (f : (a : A x) → B x a)
       → (g : (a : A y) → B y a)
       ----------------------------------------------------------------------------
       →   (f == g
               [ (λ z₁ → (x : A z₁) → B z₁ x) ↓ p ])
         ≃ ((a : A x) →
           (f a) == g (tr A p a)
                  [ (λ w → B (π₁ w) (π₂ w)) ↓ (pair= (p , refl (tr A p a))) ])

     funext-transport-dfun idp f g = eqFunExt

::

     funext-transport-dfun-l
       : (p : x == y) → (f : (a : A x) → B x a) → (g : (a : A y) → B y a)
      → (tr (λ z₁ → (x : A z₁) → B z₁ x) p f == g)
       ---------------------------------------------------------------------------
       → (a : A x) →
            (f a) == g (tr A p a)
                   [ (λ w → B (π₁ w) (π₂ w)) ↓ (pair= (p , refl (tr A p a))) ]

     funext-transport-dfun-l p f g = lemap (funext-transport-dfun p _ _)

::

     funext-transport-dfun-r
       : (p : x == y)
       → (f : (a : A x) → B x a)
       → (g : (a : A y) → B y a)
       → ((a : A x) → tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , refl (tr A p a))) (f a) == g (tr A p a))
       --------------------------------------------------------------------------
       → (tr (λ z₁ → (x : A z₁) → B z₁ x) p f == g)

     funext-transport-dfun-r p f g = remap (funext-transport-dfun p _ _)

::

   funext-transport-dfun-bezem
     : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁}{A : X → Type ℓ₂}{B : (x : X) → A x → Type ℓ₃} {x y : X}
     → (p : x == y)
     → (f : (a : A x) → B x a)
     → (g : (a : A y) → B y a)
     → (a : A y)
     ------------------------------------------------------------------------------------
     → (tr (λ x → (a : A x) → B x a) p f) a == g a
     ≃  tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , transport-inv p)) (f (tr A (! p)a)) == g a

   funext-transport-dfun-bezem idp f g a = idEqv

::

   funext-transport-dfun-bezem-l
     :  ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁}{A : X → Type ℓ₂}{B : (x : X) → A x → Type ℓ₃} {x y : X}
     → (p : x == y)
     → (f : (a : A x) → B x a)
     → (g : (a : A y) → B y a)
     → (a : A y)
     → (tr (λ x → (a : A x) → B x a) p f) a == g a
     ------------------------------------------------------------------------------------
     →  tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , transport-inv p)) (f (tr A (! p) a)) == g a

   funext-transport-dfun-bezem-l p f g a x₁ = lemap (funext-transport-dfun-bezem p f g a) x₁

::

   funext-transport-dfun-bezem-r
     :  ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁}{A : X → Type ℓ₂}{B : (x : X) → A x → Type ℓ₃} {x y : X}
     → (p : x == y)
     → (f : (a : A x) → B x a)
     → (g : (a : A y) → B y a)
     → (a : A y)
     →  tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , transport-inv p)) (f (tr A (! p) a)) == g a
     ------------------------------------------------------------------------------------
     → (tr (λ x → (a : A x) → B x a) p f) a == g a

   funext-transport-dfun-bezem-r p f g a x₁ = remap (funext-transport-dfun-bezem p f g a) x₁
