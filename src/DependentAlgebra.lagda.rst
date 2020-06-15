When ∑ and ∏ commute
~~~~~~~~~~~~~~~~~~~~

::

   {-# OPTIONS --without-K --exact-split #-}

   open import BasicTypes
   open import BasicFunctions

   open import EquivalenceType
   open import QuasiinverseType

::

   ∑-comm
     : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}
     → (B : A → Type ℓ₂) (C : A → Type ℓ₃)
       -----------------------------------------
     → Σ (Σ A B) (C ∘ fst) ≃ Σ (Σ A C) (B ∘ fst)

   ∑-comm {A = A} B C = qinv-≃ there (back , there-back , back-there)
     where
     there : Σ (Σ A B) (C ∘ fst) → Σ (Σ A C) (B ∘ fst)
     there ((a , b) , c) = ((a , c ) , b)

     back : Σ (Σ A C) (B ∘ fst) → Σ (Σ A B) (C ∘ fst)
     back  ((a , c ) , b) = ((a , b) , c)

     there-back : ∀ acb → there (back acb) == acb
     there-back ((a , c) , b) = idp

     back-there : ∀ abc → back (there abc) == abc
     back-there ((a , b) , c) = idp

   sum-commute = ∑-comm

::

   ∏-comm
     : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}
     → (B : A → Type ℓ₂)
     → (C : {a : A} → B a → Type ℓ₃)
     -----------------------------------------------------------
     → (Σ[ f ∶ Π A B ] Π[ x ∶ A ] (C (f x))) ≃ (Π[ x ∶ A ] Σ[ y ∶ B x ] C y)

   ∏-comm {A = A} B C = qinv-≃ there (back , there-back , back-there)
     where
     there : (Σ (Π A B) (\f → Π A (C ∘ f))) → (Π A (\x → Σ (B x) C))
     there (f , s) x = (f x , s x)

     back : (Π A (\x → Σ (B x) C)) → (Σ (Π A B) (\f → Π A (C ∘ f)))
     back  F = (\x → fst (F x)) , (\x → snd (F x))

     there-back : ∀ F → there (back F) == F
     there-back F = idp

     back-there : ∀ fs → back (there fs) == fs
     back-there fs = idp

::


   prod-commute = ∏-comm
