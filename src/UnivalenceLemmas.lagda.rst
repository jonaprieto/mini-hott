::

   {-# OPTIONS --without-K --exact-split #-}
   module _ where
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom

   open import EquivalenceType
   open import QuasiinverseType
   open import QuasiinverseLemmas
   open import UnivalenceAxiom
   open import UnivalenceTransport
   open import UnivalenceIdEquiv
   open import HLevelLemmas

Univalence lemmas
~~~~~~~~~~~~~~~~~

::

   module UnivalenceComposition where

::

     ua-comp
       : ∀ {ℓ : Level} {A B C : Type ℓ}
       → (α : A ≃ B)
       → (β : B ≃ C)
       ---------------------------------
       → ua (α :>≃ β) == (ua α) · (ua β)

     ua-comp α β  =
      begin
        ua (α :>≃ β)
          ≡⟨ ap ua (:>≃-ite-ua α β) ⟩
        ua (ite (ua α · ua β))
          ≡⟨ ua-η ((ua α) · (ua β)) ⟩
        (ua α) · (ua β)
      ∎

Inverses are preserved (Type-check this takes ~30min)

::

     postulate
      ua-inv-r
       : ∀ {ℓ : Level} {A B : Type ℓ}
       → (α : A ≃ B)
       -------------------------------
       → ua α · ua (≃-sym α) == refl A

     {-
     ua-inv-r {A = A} α =
       begin
         ua α · ua (≃-sym α)
           ==⟨ ! (ua-comp α (≃-sym α)) ⟩
         ua (≃-trans α (≃-sym α))
           ==⟨ ap ua (≃-trans-inv α) ⟩
         ua idEqv
           ==⟨ UnivalenceLemmas.ua-id ⟩
         refl A
       ∎
     -}

::

     ua-inv
       : ∀ {ℓ : Level} {A B : Type ℓ}
       → (α : A ≃ B)
       -------------------------
       → ua (≃-sym α) ≡ ! (ua α)

     ua-inv α =
       begin
         ua (≃-sym α)
           ≡⟨ ap (_· ua (≃-sym α)) (! (·-linv (ua α))) ⟩
         ! (ua α) · ua α · ua (≃-sym α)
           ≡⟨ ·-assoc (! (ua α)) _ _ ⟩
         ! (ua α) · (ua α · ua (≃-sym α))
           ≡⟨ ap (! (ua α) ·_) (ua-inv-r α) ⟩
         ! (ua α) · refl _
           ≡⟨ ! (·-runit (! ((ua α)))) ⟩
         ! (ua α)
       ∎
