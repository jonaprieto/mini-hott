::

   {-# OPTIONS --without-K --exact-split #-}
   open import BasicTypes
   open import BasicFunctions
   open import AlgebraOnPaths
   open import EquivalenceType
   open import HomotopyType
   open import QuasiinverseType
   open import QuasiinverseLemmas
   open import EquivalenceReasoning

Basic Equivalences
------------------

::
   module BasicEquivalences where

There are some well-known equivalences very handy about products and
coproducts.

::

     ≃-+-comm
       : ∀ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁}{Y : Type ℓ₂}
       → X + Y ≃ Y + X

     ≃-+-comm {X = X}{Y} = qinv-≃ f (g , H₁ , H₂ )
       where
       private
         f : X + Y → Y + X
         f (inl x) = inr x
         f (inr x) = inl x

         g : Y + X → X + Y
         g (inl x) = inr x
         g (inr x) = inl x

         H₁ : (f ∘ g) ∼ id
         H₁ (inl x) = idp
         H₁ (inr x) = idp

         H₂ : (g ∘ f) ∼ id
         H₂ (inl x) = idp
         H₂ (inr x) = idp

::

     ≃-+-assoc
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁}{Y : Type ℓ₂} {Z : Type ℓ₃}
       → X + (Y + Z) ≃ (X + Y) + Z

     ≃-+-assoc {X = X}{Y}{Z} = qinv-≃ f (g , (H₁ , H₂))
       where
       private
         f : X + (Y + Z) → (X + Y) + Z
         f (inl x) = inl (inl x)
         f (inr (inl x)) = inl (inr x)
         f (inr (inr x)) = inr x

         g : (X + Y) + Z → X + (Y + Z)
         g (inl (inl x)) = inl x
         g (inl (inr x)) = inr (inl x)
         g (inr x) = inr (inr x)

         H₁ : (f ∘ g) ∼ id
         H₁ (inl (inl x)) = idp
         H₁ (inl (inr x)) = idp
         H₁ (inr x) = idp

         H₂ : g ∘ f ∼ id
         H₂ (inl x) = idp
         H₂ (inr (inl x)) = idp
         H₂ (inr (inr x)) = idp

::

     ≃-+-runit
       : ∀ {ℓ₁ ℓ₂ : Level}{X : Type ℓ₁}
       → X ≃ X + (𝟘 ℓ₂)

     ≃-+-runit {ℓ₁ = ℓ₁}{ℓ₂}{X} = qinv-≃ f (g , (H₁ , H₂ ))
       where
       private
         f : X →  X + (𝟘 ℓ₂)
         f  x = inl x

         g : X + (𝟘 ℓ₂) → X
         g (inl x) = x


         H₁ : (f ∘ g) ∼ id
         H₁ (inl x) = idp

         H₂ : (x : X) → (g (f x)) ≡ x
         H₂ x = idp

::

     ≃-+-lunit
       : ∀ {ℓ₁ ℓ₂ : Level}{X : Type ℓ₁}
       → X ≃ 𝟘 ℓ₂ + X

     ≃-+-lunit {ℓ₂ = ℓ₂}{X} =
       X            ≃⟨ ≃-+-runit ⟩
       X + 𝟘 ℓ₂     ≃⟨ ≃-+-comm ⟩
       (𝟘 ℓ₂) + X   ≃∎

::

     ≃-×-comm
       : ∀ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁}{Y : Type ℓ₂}
       → X × Y ≃ Y × X

     ≃-×-comm {X = X}{Y} = qinv-≃ f (g , (H₁ , H₂))
       where
       private
         f : X × Y → Y × X
         f (x , y) = (y , x)

         g : Y × X → X × Y
         g (y , x) = (x , y)

         H₁ : (f ∘ g) ∼ id
         H₁ x = idp

         H₂ : (g ∘ f) ∼ id
         H₂ x = idp

::

     ≃-×-runit
       : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁}
       → X ≃ X × (𝟙 ℓ₂)

     ≃-×-runit {ℓ₁}{ℓ₂}{X = X} = qinv-≃ f (g , (H₁ , H₂))
       where
       private
         f : X → X × 𝟙 ℓ₂
         f x = (x , unit)

         g : X × 𝟙 ℓ₂ → X
         g (x , _) = x

         H₁ : (f ∘ g) ∼ id
         H₁ x = idp

         H₂ : (g ∘ f) ∼ id
         H₂ x = idp

::

     ≃-×-lunit
       : ∀ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁}
       → X ≃ 𝟙 ℓ₂ × X

     ≃-×-lunit {ℓ₁}{ℓ₂} {X = X} =
       X           ≃⟨ ≃-×-runit ⟩
       X × (𝟙 ℓ₂)   ≃⟨ ≃-×-comm ⟩
       (𝟙 ℓ₂) × X   ≃∎

::

     ≃-×-assoc
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁}{Y : Type ℓ₂} {Z : Type ℓ₃}
       → X × (Y × Z) ≃ (X × Y) × Z

     ≃-×-assoc {X = X}{Y}{Z} = qinv-≃ f (g , (H₁ , H₂))
       where
       private
         f : X × (Y × Z) → (X × Y) × Z
         f (x , (y , z)) = ( (x , y) , z)

         g : (X × Y) × Z → X × (Y × Z)
         g ((x , y) , z) = (x , (y , z))

         H₁ : (f ∘ g) ∼ id
         H₁ ((x , y) , z) = idp

         H₂ : g ∘ f ∼ id
         H₂ (x , (y , z)) = idp

::

     ≃-×-+-distr
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁}{Y : Type ℓ₂} {Z : Type ℓ₃}
       → (X × (Y + Z)) ≃ ((X × Y) + (X × Z))

     ≃-×-+-distr {X = X}{Y}{Z} = qinv-≃ f (g , (H₁ , H₂))
       where
       private
         f : (X × (Y + Z)) → ((X × Y) + (X × Z))
         f (x , inl y) = inl (x , y)
         f (x , inr z) = inr (x , z)

         g : ((X × Y) + (X × Z)) → (X × (Y + Z))
         g (inl (x , y)) = x , inl y
         g (inr (x , z)) = x , inr z

         open import CoproductIdentities
         H₁ : (f ∘ g) ∼ id
         H₁ (inl x) = ap inl (uppt x )
         H₁ (inr x) = ap inr (uppt x)

         H₂ : (g ∘ f) ∼ id
         H₂ (p , inl x) = pair= (idp , idp)
         H₂ (p , inr x) = pair= (idp , idp)

A type and its lifting to some universe are equivalent as types.

::

     lifting-equivalence
       : ∀ {ℓ₁ ℓ₂ : Level}
       → (A : Type ℓ₁)
       → A ≃ (↑ ℓ₂ A)

     lifting-equivalence {ℓ₁}{ℓ₂} A =
       quasiinverse-to-≃ f (g , (λ { (Lift a) → idp}) , λ {p → idp})
       where
       f : A → ↑ ℓ₂ A
       f a = Lift a

       g : A ← ↑ ℓ₂ A
       g (Lift a) = a

Some synomys:

::

     ≃-↑ = lifting-equivalence

::

     move-right-from-composition
      : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
      → (f : A → B) → (e : B ≃ C) → (g : A → C)
      → f :> (e ∙→) ≡ g
      --------------------------------------
      →           f ≡ g :> (e ∙←)

     move-right-from-composition f e .(λ x → π₁ e (f x)) idp =
       begin
        f
          ≡⟨⟩
        f :> id
          ≡⟨ ap (λ w → f :> w) (funext (λ x → ! (rlmap-inverse-h e x))) ⟩
        f :> ((e ∙→) :> (e ∙←))
          ≡⟨ :>-lassoc f (e ∙→) (e ∙←) ⟩
        (f :> (e ∙→)) :> (e ∙←)
        ∎ where open import FunExtAxiom

     move-left-from-composition
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (f : A → B) → (e : B ≃ C) → (g : A → C)
        →           f ≡ g :> (e ∙←)
        --------------------------------------
        → f :> (e ∙→) ≡ g

     move-left-from-composition .(λ x → π₁ (π₁ (π₂ e (g x)))) e g idp
        = :>-rassoc g (e ∙←) (e ∙→)
          · ap (λ w → g :> w) (funext (λ x → lrmap-inverse-h e x))
        where open import FunExtAxiom


::

     2-out-of-3-property
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (f : A → C) → (e : A ≃ B) → (g : B ≃ C)
        → f ≡ (e ∙→) :> (g ∙→)
        -------------------------
        → isEquiv f

     2-out-of-3-property .(λ x → π₁ g (π₁ e x)) e g idp = comp-is-equiv
        where
        comp-is-equiv : isEquiv ((e ∙→) :> (g ∙→))
        comp-is-equiv = π₂ (≃-trans e g)

::

     inv-of-equiv-composition
        : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
        → (f : A ≃ B)
        → (g : B ≃ C)
        → remap ((f ∙→) :> (g ∙→) ,  π₂ (≃-trans f g))
          ≡ (g ∙←) :> (f ∙←)
     inv-of-equiv-composition f g = idp

