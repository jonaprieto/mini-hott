Rewriting
---------

We can define Higher inductive types in Agda by rewriting method, same
approach as in [HoTT-Agda]. However, this is unsafe.

::

   {-# OPTIONS --without-K --exact-split --rewriting #-}
   module Rewriting where

::

     open import BasicTypes

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
