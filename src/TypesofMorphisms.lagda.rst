::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import QuasiinverseType
   open import DecidableEquality
   open import NaturalType
   open import HLevelTypes
   open import HLevelLemmas
   open import HedbergLemmas
   open import TruncationType
   open import FibreType
   open import CoproductIdentities

Types of Morphisms
------------------

::

   module TypesofMorphisms where

Surjections
~~~~~~~~~~~

::

     isSurjection
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (f : A → B)
       → Type (ℓ₁ ⊔ ℓ₂)

     isSurjection {B = B} f = (b : B) → ∥ fib f b ∥

     isSurjective   = isSurjection
     isOnto         = isSurjection
     _is-surjection = isSurjection

Do not confuse with the traditional logic notation for surjective
functions which says :math:`f` is surjective if
:math:`∀ (b : B) ∃ (a : A) . f a ≡ b`. This is stronger than merely know
exists an :math:`(a : A)` as it was stated above with ``∥ fib f b ∥``.

Therefore, we define the concept of *split-surjection*:

::

     isSplitSurjection
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (f : A → B)
       → Type (ℓ₁ ⊔ ℓ₂)

     isSplitSurjection {B = B} f = (b  : B) → fib f b

     _is-split-surjection = isSplitSurjection

Which is equivalent to say :math:`f` is a **retraction**:

::

     isRetraction
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (f : A → B)
       → Type (ℓ₁ ⊔ ℓ₂)

     isRetraction {A = A}{B} f = ∑ (B → A) (λ g → (b : B) → f (g b) ≡ b)

     _is-retraction = isRetraction

As a trivial example, we know the identity function is indeed a
surjective function. Let us check this.

::

     identity-is-surjective : ∀ {ℓ : Level}{A : Type ℓ} →  isSurjection {A = A} id
     identity-is-surjective {A = A} b = ∥∥-intro (b , idp)

Embeddings
~~~~~~~~~~

::

     isEmbedding
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (f : A → B)
       ---------------
       → Type (ℓ₁ ⊔ ℓ₂)

     isEmbedding {A = A} f = ∀ {x y : A} → isEquiv (ap f {x}{y})

     _is-embedding = isEmbedding

Injections
~~~~~~~~~~

**Discuss**: should I demand for injective functions to have their
domains and codomains as sets?

::

     isInjective
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (f : A → B)
       → Type (ℓ₁ ⊔ ℓ₂)

     isInjective {A = A} f = ∀ {x y} → f x ≡ f y → x ≡ y

     _is-injective = isInjective

As a trivial example, let us prove identity is an injective function:

::

     identity-is-injective
       : ∀ {ℓ : Level} {A : Type ℓ}
       → isInjective {A = A} id

     identity-is-injective p = p

::

     isInjectiveIsProp
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (iA : isSet A)
       → (f : A → B)
       ------------------------
       → isProp (isInjective f)

     isInjectiveIsProp {A = A}{B} iA f i1 i2 =
       aux i1 i2
       where
         private
           aux : isProp (∀ {x y} → (f x ≡ f y → x ≡ y))
           aux = pi-is-prop-implicit
                  (λ x → pi-is-prop-implicit (λ y →
                    pi-is-prop (λ p → iA x y)
                  ))

     injective-is-prop = isInjectiveIsProp

::

     isSurjectionIsProp
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (f : A → B)
       → isProp (isSurjection f)

     isSurjectionIsProp f = pi-is-prop (λ b → truncated-is-prop {A = fib f b})

     surjective-is-prop = isSurjectionIsProp

If the function :math:`f : A → B` is a surjection, we are able to get a
function :math:`g : B → A` by the recursion principle of truncation.

::

     fromSurjection
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (f : A → B)
       → isSet B
       → isSurjection f
       → isInjective f
       --------------------------------
       → (b : B) → ∑ A (λ a → f a == b)

     fromSurjection {A = A}{B} f iB f-is-onto f-is-injective b
       = trunc-rec (aux b) id (f-is-onto b)
       where
       private
         aux
           : (b : B)
           → isProp (fib f b)

         aux .(f x) (x , idp) (x' , p2) =
           ∑-≡
             (λ y → f y == f x)
             (f-is-injective (! p2))
             (iB (f x') (f x)
                 (tr (λ z₁ → f z₁ == f x) (f-is-injective (! p2)) idp) p2)

::

     preimage-function = fromSurjection

Bijections
~~~~~~~~~~

Bijection is a concept from Set Theory, which meeans that if we want to
define it in Univalent Type Theory, we must talk about only functions
between (homotopy) sets. Thus, we will find these assumptions in the
type for bijections, even though, we do not really need them ¬¬.

::

     isBijection
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (f : A → B)
       → isSet A → isSet B
       -------------------
       → Type (ℓ₁ ⊔ ℓ₂)

     isBijection f iA iB = isInjective f × isSurjection f

     _is-bijection = isBijection

Before to proceed to prove that *equivalence* and *bijection* are two
logical equivalent concept when we talk about (homotopy) sets, let us
give an example of a natural bijection, the idenitity function.

::

     identity-is-bijection
       : ∀ {ℓ : Level} {A : Type ℓ}
       → (A-is-set : isSet A)
       → isBijection id A-is-set A-is-set

     identity-is-bijection {A} ia = identity-is-injective , identity-is-surjective

**Discuss**: we again see that the assumption of being a set for the
domain is required in the way to check the funciton is injective or
surjective. This must suggest, we must include this assumption in the
Injective definition.

::

     Bijection
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (iA : isSet A) → (iB : isSet B)
       → (f : A → B)
       → isBijection f iA iB
       ----------------------
       → A ≃ B

     Bijection {A = A}{B} iA iB f (f-is-injective , f-is-onto)
       = qinv-≃ f (g , (H₁ , H₂))
       where
       aux : (b : B) → ∑ A (λ a → f a ≡ b)
       aux = fromSurjection f iB f-is-onto f-is-injective

       g : B → A
       g = π₁ ∘ aux

       H₁ : (b : B) → f (g b) == b
       H₁ b = π₂ (aux b)

       H₂ : (a : A) → g (f a) == a
       H₂ a = f-is-injective (H₁ (f a))

::

     is-bijection-to-≃ =  Bijection

::

     ≃-to-bijection
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (iA : isSet A)
       → (iB : isSet B)
       -----------------------------------------
       → (e : A ≃ B) → (isBijection (e ∙→) iA iB)

     ≃-to-bijection iA iB e =
       (λ {x y} p  → ! (∙←∘∙→ e) · (ap (e ∙←) p)  · (∙←∘∙→ e) )  -- is injective
       , λ b → ∣ (e ∙←) b , ∙→∘∙← e ∣                            -- is surjective
       where open import EquivalenceType

Bijection and being equivalent are equivalent notions:

::

     isBijection-≃-isEquiv
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (iA : isSet A) (iB : isSet B)
       → (f : A → B)
       ----------------------------------
       → isBijection f iA iB  ≃ isEquiv f

     isBijection-≃-isEquiv {A = A}{B} iA iB f =
       qinv-≃
         (λ bij → π₂ (Bijection iA iB f bij))
         ((λ isEquivf → ≃-to-bijection iA iB (f , isEquivf))
         , h1 , h2)
       where
         h1 : (λ x → π₂ (Bijection iA iB f (≃-to-bijection iA iB (f , x)))) ∼ id
         h1 e = isContrMapIsProp f _ e

         h2 : (λ x → ≃-to-bijection iA iB (f , π₂ (Bijection iA iB f x))) ∼ id
         h2 bij = ×-is-prop (isInjectiveIsProp iA f) (isSurjectionIsProp f) _ bij

     open import QuasiinverseLemmas

::

     bijIsProp
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (iA : isSet A)(iB : isSet B)
       → (f : A → B)
       ------------------------------
       → isProp (isBijection f iA iB)

     bijIsProp iA iB f = isProp-≃ (≃-sym (isBijection-≃-isEquiv iA iB f)) (isEquivIsProp f)
     bijection-is-prop = bijIsProp

For some reasons, we might need to have the inverse, the actual
function, of a bijection. One way I see now is to recover such a
function from the equivalence, using ``remap``. Let’s see this:

::

     inverse-of-bijection
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (iA : isSet A) → (iB : isSet B)
       → (f : A → B)
       → isBijection f iA iB
       ------------------------------
       → B → A

     inverse-of-bijection iA iB f isBij
       = remap (Bijection iA iB f isBij)

     inv-of-bij = inverse-of-bijection

::

     ∘-bijective-and-its-inverse-l
         : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
         → (A-is-set : isSet A) → (B-is-set : isSet B)
         → (f : A → B) → (f-is-bij : isBijection f A-is-set B-is-set)
         --------------------------------------------------------
         → f ∘ inverse-of-bijection A-is-set B-is-set f f-is-bij ∼ id

     ∘-bijective-and-its-inverse-l A-is-set B-is-set f f-is-bij =
       lrmap-inverse-h (is-bijection-to-≃ A-is-set B-is-set f f-is-bij)

::

     ∘-bijective-and-its-inverse-r
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
       → (A-is-set : isSet A)(B-is-set : isSet B)
       → (f : A → B) → (f-is-bij : isBijection f A-is-set B-is-set)
       ------------------------------------------------------------
       → (inverse-of-bijection A-is-set B-is-set f f-is-bij) ∘ f ∼ id

     ∘-bijective-and-its-inverse-r A-is-set B-is-set f f-is-bij =
       rlmap-inverse-h (is-bijection-to-≃ A-is-set B-is-set f f-is-bij)

The inverse of a bijection is clearly a bijection as well.

::

     inverse-of-bijection-is-bijection
       : ∀ {ℓ₁ ℓ₂ : Level}{A : Type ℓ₁}{B : Type ℓ₂}
       → (A-is-set : isSet A) → (B-is-set : isSet B)
       → (f : A → B) → (f-is-bij : isBijection f A-is-set B-is-set)
       ------------------------------------------------------------
       → isBijection (inverse-of-bijection A-is-set B-is-set f f-is-bij) B-is-set A-is-set

     inverse-of-bijection-is-bijection A-is-set B-is-set f f-is-bij
       = inv-f-is-inj , inv-f-is-sur
       where

       inv-f-is-inj : isInjective (inverse-of-bijection A-is-set B-is-set f f-is-bij)
       inv-f-is-inj {x = x}{y} p =
         ! ∘-bijective-and-its-inverse-l A-is-set B-is-set f f-is-bij x
         ·  ap f p
         · ∘-bijective-and-its-inverse-l A-is-set B-is-set f f-is-bij y

       inv-f-is-sur : isSurjection (inverse-of-bijection A-is-set B-is-set f f-is-bij)
       inv-f-is-sur a = ∣ f a , ∘-bijective-and-its-inverse-r A-is-set B-is-set f f-is-bij a ∣

::

     ∘-injectives-is-injective
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level }
       → {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
       → (f : A → B) → isInjective f
       → (g : B → C) → isInjective g
       -----------------------------
       → isInjective (g ∘ f)

     ∘-injectives-is-injective f f-is-injective g g-is-injective
       p = f-is-injective (g-is-injective p)

As we expect, composition of surjections is also surjections. However,
this fact is not trivial and it is a good exercise to understand better
propositional truncation.

::

     ∘-surjection-is-surjection
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level }
       → {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
       → (f : A → B) → isSurjection f
       → (g : B → C) → isSurjection g
       -----------------------------
       → isSurjection (g ∘ f)

     ∘-surjection-is-surjection {A = A}{B}{C} f f-is-surjection g g-is-surjection
       c = step₁ (g-is-surjection c)
       where
       step₁ : ∥ ∑ B (λ b → g b ≡ c) ∥ → ∥ ∑ A (λ a → (f :> g) a ≡ c) ∥
       step₁ = trunc-rec ∥∥-is-prop step₂
         where
         step₂ : ∑ B (λ b → g b ≡ c) → ∥ ∑ A (λ a → (f :> g) a ≡ c) ∥
         step₂ (b , p₁) = step₃ b p₁ (f-is-surjection b)
           where
           step₃ : (b : B) → g b ≡ c
             → ∥ ∑ A (λ a → f a ≡ b) ∥ → ∥ ∑ A (λ a → (f :> g) a ≡ c) ∥
           step₃ b p₁ = trunc-rec ∥∥-is-prop step₄
              where
              step₄ : ∑ A (λ a → f a ≡ b) → ∥ ∑ A (λ a → (f :> (λ {a = a₁} → g)) a ≡ c) ∥
              step₄ (a , p) = ∣ a , ((ap g p) · p₁) ∣

Lastly, bijections is also closed by compositions but its proof is just
application of the lemmas proved above. Notice the extra requirement
which is the domain and codomains need to be sets. This was not stated
above for the related lemmas, but it the condition to talk about the
concept of bijection.

::

     ∘-bijections-is-bijection
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}
       → {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
       → (A-is-set : isSet A) (B-is-set : isSet B)(C-is-set : isSet C)
       → (f : A → B) → isBijection f A-is-set B-is-set
       → (g : B → C) → isBijection g B-is-set C-is-set
       -----------------------------------------------
       → isBijection (g ∘ f) A-is-set C-is-set

     ∘-bijections-is-bijection {A = A}{B}{C}
       A-is-set B-is-set iC
         f (f-is-injective , f-is-surjection)
         g (g-is-injective , g-is-surjection)
       = ∘-injectives-is-injective f f-is-injective g g-is-injective
       , ∘-surjection-is-surjection f f-is-surjection g g-is-surjection

Other theorems about +-map

::

     inj-from-⊕-injective
       : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
       → {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃} {D : Type ℓ₄}
       → {f : A + B → C + D}
       → (isInjective f)
       ---------------------------
       → (g : B → D) → ((b : B) → inr (g b) ≡ f (inr b))
       → isInjective g

     inj-from-⊕-injective {C = C} f⊕g-is-inj g g-is-f {x} {y} p  =
        inr-is-injective
         (f⊕g-is-inj {x = inr x} (! g-is-f x · ap inr p · g-is-f y))

::

     right-is-injective-of-⊕-injective
       : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
       → {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃} {D : Type ℓ₄}
       → {f : A → C} {g : B → D}
       → (isInjective 〈 f ⊕ g 〉)
       ---------------------------
       → isInjective g

     right-is-injective-of-⊕-injective {C = C} f⊕g-is-inj {x} {y} p =
       inr-is-injective
         (f⊕g-is-inj {x = inr x}
           $ ap (λ w → inr {A = C} w) p)

.. code:: text

     left-is-injective-of-⊕-injective
       : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
       → {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃} {D : Type ℓ₄}
       → {f : A → C} {g : B → D}
       → (isInjective 〈 f ⊕ g 〉)
       ---------------------------
       → isInjective f

     left-is-injective-of-⊕-injective {C = C} f⊕g-is-inj {x} {y} p =
       inl-is-injective
         (f⊕g-is-inj {x = inl x}
           $ ap (λ w → inl {A = C} w) p)

::

     :>-is-injective-is-inj
       : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁}{B : Type ℓ₂}{C : Type ℓ₃}
       → {f : A → B} {g : B → C }
       → isInjective (f :> g)
       ----------------------
       → isInjective f

     :>-is-injective-is-inj {f = f} {g} :>-is-inj p = :>-is-inj (ap g p)
