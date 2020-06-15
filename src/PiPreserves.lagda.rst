::

   {-# OPTIONS --without-K --exact-split #-}

   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import QuasiinverseType

Equivalence with Pi type
------------------------

::

   module PiPreserves {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{C : A → Type ℓ₂}{D : A → Type ℓ₃}
       (e : (a : A) → (C a ≃ D a)) where

     private
       f : (a : A) → C a → D a
       f a = lemap (e a)

       f⁻¹ : (a : A) → D a → C a
       f⁻¹ a = remap (e a)

       α : (a : A) → (f a) ∘ (f⁻¹ a) ∼ id
       α a x = lrmap-inverse (e a)

       β : (a : A) → (f⁻¹ a) ∘ (f a) ∼ id
       β a x = rlmap-inverse (e a)

       ΠAC→ΠAD : Π A C → Π A D
       ΠAC→ΠAD p = λ a → (f a) (p a)

       ΠAD→ΠAC : Π A D → Π A C
       ΠAD→ΠAC p = λ a → (f⁻¹ a) (p a)

       H₁ : ΠAC→ΠAD ∘ ΠAD→ΠAC ∼ id
       H₁ p =
         begin
           (ΠAC→ΠAD ∘ ΠAD→ΠAC) p
             ==⟨ idp ⟩
           ΠAC→ΠAD (λ a → (f⁻¹ a) (p a))
             ==⟨ idp ⟩
           (λ aa → (f aa) (f⁻¹ aa (p aa)))
             ==⟨ funext (λ x → α x (p x)) ⟩
           (λ aa → p aa)
         ∎

       H₂ : ΠAD→ΠAC ∘ ΠAC→ΠAD ∼ id
       H₂ p =
         begin
           (ΠAD→ΠAC ∘ ΠAC→ΠAD) p
             ==⟨ idp ⟩
           ΠAD→ΠAC (λ a → (f a) (p a))
             ==⟨ idp ⟩
           (λ aa → (f⁻¹ aa) (f aa (p aa)))
             ==⟨ funext (λ x → β x (p x)) ⟩
           (λ aa → p aa)
         ∎

::

     pi-equivalence
       : Π A C ≃ Π A D -- by (e : (a : A) → (C a ≃ D a))

     pi-equivalence = qinv-≃ ΠAC→ΠAD (ΠAD→ΠAC , H₁ , H₂)
