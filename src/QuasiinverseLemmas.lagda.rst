Quasiinverse Lemmas
~~~~~~~~~~~~~~~~~~~

Two functions are quasi-inverses if we can construct a function
providing ``(g ∘ f) x = x`` and ``(f ∘ g) y = y`` for any given ``x``
and ``y``.

::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import HomotopyLemmas


   open import QuasiinverseType

Equivalence composition
-----------------------

::

   module QuasiinverseLemmas where

The equivalence types are indeed equivalence

::

     qinv-comp
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
       → Σ (A → B) qinv
       → Σ (B → C) qinv
       ----------------
       → Σ (A → C) qinv

     qinv-comp (f , (if , (εf , ηf))) (g , (ig , (εg , ηg))) = (g ∘ f) , ((if ∘ ig) ,
        ( (λ x → ap g (εf (ig x)) · εg x)
        ,  λ x → ap if (ηg (f x)) · ηf x))

::

     qinv-inv
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → Σ (A → B) qinv
       ----------------
       → Σ (B → A) qinv

     qinv-inv (f , (g , (ε , η))) = g , (f , (η , ε))

Equivalence types are equivalence relations.

::

     idEqv
       : ∀ {ℓ} {A : Type ℓ}
       -------
       → A ≃ A

     idEqv = id , λ a → (a , refl a) , λ { (_ , idp) → refl (a , refl a) }

More syntax:

::

     ≃-refl = idEqv
     A≃A    = idEqv

::

     _:>≃_ ≃-trans
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
       → A ≃ B
       → B ≃ C
       -------
       → A ≃ C

     _:>≃_ {A = A} {C = C} eq-f eq-g = qinv-≃ (π₁ qcomp) (π₂ qcomp)
      where
        qcomp : Σ (A → C) qinv
        qcomp = qinv-comp (≃-qinv eq-f) (≃-qinv eq-g)

More syntax:

::

     compEqv = _:>≃_
     ≃-trans = _:>≃_

::

     ≃-sym
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → A ≃ B
       -------
       → B ≃ A

     ≃-sym {ℓ}{_} {A} {B} eq-f = qinv-≃ (π₁ qcinv) (π₂ qcinv)
      where
        qcinv : Σ (B → A) qinv
        qcinv = qinv-inv (≃-qinv eq-f)

More syntax:

::

     invEqv = ≃-sym
     ≃-flip = ≃-sym
