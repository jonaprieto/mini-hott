Equivalences preserved by Sigma types
-------------------------------------

::

   {-# OPTIONS --without-K --exact-split #-}
   module _ where

   open import TransportLemmas
   open import ProductIdentities
   open import CoproductIdentities

   open import EquivalenceType

   open import HomotopyType
   open import HomotopyLemmas

   open import HalfAdjointType
   open import QuasiinverseType
   open import QuasiinverseLemmas

::

   module
     SigmaPreserves {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{C : A → Type ℓ₂}{D : A → Type ℓ₃}
       (e : (a : A) → C a ≃ D a)
     where

     private
       f : (a : A) → C a → D a
       f a = lemap (e a)

       f⁻¹ : (a : A) → D a → C a
       f⁻¹ a = remap (e a)

       α : (a : A) → (f a) ∘ (f⁻¹ a) ∼ id
       α a x = lrmap-inverse (e a)

       β : (a : A) → (f⁻¹ a) ∘ (f a) ∼ id
       β a x = rlmap-inverse (e a)

       ΣAC-to-ΣAD :  Σ A C → Σ A D
       ΣAC-to-ΣAD (a , c) = (a , (f a) c)

       ΣAD-to-ΣAC :  Σ A D → Σ A C
       ΣAD-to-ΣAC (a , d) = (a , (f⁻¹ a) d)

       H₁ : ΣAC-to-ΣAD ∘ ΣAD-to-ΣAC ∼ id
       H₁ (a , d) = pair= (idp , α a d)

       H₂ : ΣAD-to-ΣAC ∘ ΣAC-to-ΣAD ∼ id
       H₂ (a , c) = pair= (idp , β a c)

::

     sigma-preserves
       : Σ A C ≃ Σ A D

     sigma-preserves = qinv-≃ ΣAC-to-ΣAD (ΣAD-to-ΣAC , H₁ , H₂)

   open SigmaPreserves

If

.. math:: A\,,~B : U

\ and

.. math:: C: A → U

and

.. math:: e: B \simeq A

, then

{: .equation }

.. math:: \Sigma\,{A}\,C\,\simeq\,\Sigma\,B\,(C ∘ e).

::

   module SigmaPreserves-≃ {ℓ₁ ℓ₂ ℓ₃}
     {A : Type ℓ₁} {B : Type ℓ₂} (e : B ≃ A) {C : A → Type ℓ₃} where

     private
       f : B → A
       f = lemap e

       ishaef : ishae f
       ishaef = ≃-ishae e

       f⁻¹ : A → B
       f⁻¹ = ishae.g ishaef

       α : f ∘ f⁻¹ ∼ id
       α = ishae.ε ishaef

       β : f⁻¹ ∘ f  ∼ id
       β = ishae.η ishaef

       τ : (b : B) → ap f (β b) == α (f b)
       τ = ishae.τ ishaef

     ΣAC-to-ΣBCf : Σ A C → Σ B (λ b → C (f b))
     ΣAC-to-ΣBCf (a , c) = f⁻¹ a , c'
       where
         c' : C (f (f⁻¹ a))
         c' = transport C ((α a) ⁻¹) c

     ΣBCf-to-ΣAC : Σ B (λ b → C (f b)) → Σ A C
     ΣBCf-to-ΣAC (b , c') = f b , c'

     private
       H₁ : ΣAC-to-ΣBCf ∘ ΣBCf-to-ΣAC ∼ id
       H₁ (b , c') = pair= (β b , patho)
         where
         c'' : C (f (f⁻¹ (f b)))
         c'' = transport C ((α (f b)) ⁻¹) c'

         -- patho : c'' == c' [ (C ∘ f) ↓ (β b)]
         patho : transport (λ x → C (f x)) (β b) c'' == c'
         patho =
           begin
             transport (λ x → C (f x)) (β b) c''
               ==⟨ transport-family (β b) c'' ⟩
             transport C (ap f (β b)) c''
               ==⟨ ap (λ γ → transport C γ c'') (τ b) ⟩
             transport C (α (f b)) c''
               ==⟨ transport-comp-h ((α (f b)) ⁻¹) (α (f b)) c' ⟩
             transport C ( ((α (f b)) ⁻¹) · α (f b)) c'
               ==⟨ ap (λ γ → transport C γ c') (·-linv (α (f b))) ⟩
             transport C idp c'
               ==⟨⟩
             c'
           ∎

     private
       H₂ : ΣBCf-to-ΣAC ∘ ΣAC-to-ΣBCf ∼ id
       H₂ (a , c) = pair= (α a , patho)
         where
         patho : transport C (α a) (transport C ((α a) ⁻¹) c) == c
         patho =
           begin
             transport C (α a) (transport C ((α a) ⁻¹) c)
               ==⟨ transport-comp-h (((α a) ⁻¹)) (α a) c ⟩
             transport C ( ((α a) ⁻¹) · (α a) ) c
               ==⟨ ap (λ γ → transport C γ c) (·-linv (α a)) ⟩
             transport C idp c
               ==⟨⟩
             c
           ∎

::

     sigma-preserves-≃
       : Σ A C ≃ Σ B (λ b → C (f b))

     sigma-preserves-≃ = qinv-≃ ΣAC-to-ΣBCf (ΣBCf-to-ΣAC , H₁ , H₂)


::

   sigma-maps-≃
     : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {A' : Type ℓ₄} {B : A → Type ℓ₂}{B' : A' → Type ℓ₃}
     → (α : A ≃ A')
     → ((a : A) → (B a ≃ B' ((α ∙) a)))
     ----------------------------------
     → Σ A B ≃ Σ A' B'

   sigma-maps-≃ {A = A}{A'}{B}{B'} α β =
     ≃-trans (sigma-preserves β) (≃-sym (sigma-preserves-≃ α))
     where
       open SigmaPreserves
       open SigmaPreserves-≃
