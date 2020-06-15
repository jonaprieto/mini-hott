::

   {-# OPTIONS --without-K --exact-split #-}
   open import Transport
   open import HomotopyType

Composition with homotopies
~~~~~~~~~~~~~~~~~~~~~~~~~~~

::

   hl-comp
     : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂} {C : Type ℓ₃}
     → {f g : A → B}
     → {j k : B → C}
     → f ∼ g
     → j ∼ k
     -------------------
     → (j ∘ f) ∼ (k ∘ g)

   hl-comp {g = g}{j = j} f-g j-k = λ x → ap j (f-g x) · j-k (g x)

::

   rcomp-∼
     : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂} {C : Type ℓ₃}
     → (f : A → B)
     → {j k : B → C}
     → j ∼ k
     -------------------
     → (j ∘ f) ∼ (k ∘ f)

   rcomp-∼ f j-k = hl-comp (h-refl f) j-k

::

   lcomp-∼
     : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂} {C : Type ℓ₃}
     → {f g : A → B}
     → (j : B → C)
     → f ∼ g
     -------------------
     → (j ∘ f) ∼ (j ∘ g)

   lcomp-∼ j α = hl-comp α (h-refl j)

Naturality
~~~~~~~~~~

Homotopy is natural, meaning that it satisfies the following square
commutative diagram.

::

   h-naturality
     : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
     → {f g : A → B} → {x y : A}
     → (H : f ∼ g)
     → (p : x == y)
     ------------------------------
     → H x · ap g p == ap f p · H y

   h-naturality {x = x} H idp = ! (·-runit (H x))

A particular case of naturality on the identity function.

::

   h-naturality-id
     : ∀ {ℓ : Level} {A : Type ℓ}  {f : A → A} → {x : A}
     → (H : f ∼ id)
     -----------------------
     → H (f x) == ap f (H x)

   h-naturality-id {f = f} {x = x} H =
     begin
       H (f x)
         ==⟨ ·-runit (H (f x)) ⟩
       H (f x) · refl (f x)
         ==⟨ ap (H (f x) ·_) (! (·-rinv (H x))) ⟩
       H (f x) · ((H x) · (! (H x)))
         ==⟨ ap (H (f x) ·_) (ap (_· (! (H x))) (! ap-id (H x))) ⟩
       H (f x) · (ap id (H x) · ! (H x))
         ==⟨ ! (·-assoc (H (f x)) (ap id (H x)) (! (H x))) ⟩
       (H (f x) · ap id (H x)) · ! (H x)
         ==⟨ ·-right-to-left-r (h-naturality H (H x)) ⟩
       ap f (H x)
     ∎
