Rewriting
---------

We can define Higher inductive types in Agda by rewriting method, same
approach as in [HoTT-Agda]. However, this is unsafe.

::

   {-# OPTIONS --without-K --exact-split --rewriting #-}
   module Rewriting where

::

     open import BasicTypes
     open import BasicFunctions

{: .axiom}

::

     infix 30 _↦_
     postulate
       _↦_
         : ∀ {ℓ : Level} {A : Type ℓ}
         → A → A
         -------
         → Type ℓ

     {-# BUILTIN REWRITE _↦_ #-}



For convenience, we add the following rewriting rule.

::

     postulate
          runit
            : ∀ {ℓ : Level} {A : Type ℓ}  {a a' : A}
            → {p : a == a'}
            --------------
            → p · idp ↦ p

     {-# REWRITE runit #-}