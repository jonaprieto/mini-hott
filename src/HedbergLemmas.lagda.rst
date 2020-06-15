Hedberg theorem
---------------

::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType
   open import HLevelTypes
   open import RelationType
   open import FunExtAxiom
   open import FunExtTransport

   module
     HedbergLemmas
     where
     module
       HedbergLemmas2
       where

A set is a type when it holds Axiom K.

::

       axiomKisSet
         : ∀ {ℓ : Level} {A : Type ℓ}
         → ((a : A) → (p : a == a) → p == refl a)
         → isSet A

       axiomKisSet k x _ p idp = k x p

::

       reflRelIsSet
         : ∀ {ℓ : Level} (A : Type ℓ)
         → (r : Rel A)
         → ((x y : A) → R {{r}} x y → x == y)  -- xRy ⇒ Id(x,y)
         →   ((x : A) → R {{r}} x x)           -- ∀ x ⇒ xRx
         ------------------------------------
         → isSet A

       reflRelIsSet A r f ρ x .x p idp = lemma p
         where
         lemma2
           : {a : A}
           → (p : a == a) → (o : R {{r}} a a)
           → (f a a o) == f a a (transport (R {{r}} a) p o)
                        [ (λ x → a == x) ↓ p ]

         lemma2 {a} p = funext-transport-l p (f a a) (f a a) (apd (f a) p)

         lemma3
           :  {a : A}
           → (p : a == a)
           → (f a a (ρ a)) · p == (f a a (ρ a))

         lemma3 {a} p = inv (transport-concat-r p _) · lemma2 p (ρ a) ·
                          ap (f a a) (Rprop {{r}} a a _ (ρ a))

         lemma
           : {a : A}
           → (p : a == a)
           → p == refl a

         lemma {a} p = ·-cancellation ((f a a (ρ a))) p (lemma3 p)

Lema: if a type is decidable, then ¬¬A is actually A.

::

       lemDoubleNeg
         : ∀ {ℓ : Level} {A : Type ℓ}
         → (A + ¬ A)
         ---------------
         → (¬ (¬ A) → A)

       lemDoubleNeg (inl x) _ = x
       lemDoubleNeg (inr f) n = exfalso (n f)

     open HedbergLemmas2 public

-  Hedberg’s theorem. A type with decidable equality is a set.

::

     hedberg
       : ∀ {ℓ : Level} {A : Type ℓ}
       → ((a b : A) → (a ≡ b) + ¬ (a ≡ b))
       -----------------------------------
       → isSet A

     hedberg {ℓ}{A = A} f
       = reflRelIsSet A
           (record { R = λ a b → ¬ (¬ (a == b))
                   ; Rprop = isPropNeg })
                   doubleNegEq (λ a z → z (refl a))

       where
       doubleNegEq
        : (a b : A) → ¬ (¬ (a == b))
        → (a == b)

       doubleNegEq a b p = lemDoubleNeg (f a b) p

       isPropNeg
         : (a b : A)
         → isProp (¬ (¬ (a == b)))

       isPropNeg a b x y = funext λ u → exfalso (x u)

More syntax:

::

     decidable-is-set = hedberg
