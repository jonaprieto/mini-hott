::

   {-# OPTIONS --without-K --exact-split #-}
   module _ where

   open import BasicTypes
   open import BasicFunctions

Hlevel types
------------

Higher levels of the homotopical structure:

-  Contractible types (:math:`-2`)
-  Propositions (:math:`-1`)
-  Sets (:math:`0`)
-  Groupoids (:math:`1`)

Contractible types
~~~~~~~~~~~~~~~~~~

A *contractible* type is a type such that **every** element is equal to
a point, the *center* of contraction.

::

   isContr
     : ∀ {ℓ : Level} (A : Type ℓ)
     --------------
     → Type ℓ

   isContr A = Σ A (λ a → ((x : A) → a == x))

Synonym:

::

   Contractible = isContr
   is-singleton = isContr
   isSingleton  = isContr
   _is-contr    = isContr

   center-of
     : ∀ {ℓ : Level}
     → {A : Type ℓ}
     → A is-contr
     → A
   center-of (a , _) = a


If a type is contractible, any of its points is a center of contraction:

<img “src=”assets/images/issinglenton.png" width=“400” align=“right”>

::

   contr-connects
     : ∀ {ℓ : Level} {A : Type ℓ}
     → A is-contr
     ----------------------
     → (a a' : A) → a ≡ a'

   contr-connects (c₁ , f) c₂ x = ! (f c₂) · (f x)

Propositions
~~~~~~~~~~~~

A type is a *mere proposition* if any two inhabitants of the type are
equal.

::

   isProp
     : ∀ {ℓ : Level} (A : Type ℓ) → Type ℓ

   isProp A = ((x y : A) → x == y)

More syntax:

::

   is-subsingleton = isProp
   isSubsingleton  = isProp
   _is-prop         = isProp

Let’s stop a bit. So, these propositios, also named “mere” propositions
tell us: in a proposition, its elements are connected with each other.
Subsinglenton (which is, subset of a singlenton (a unit point set)) is
empty or it has the element. Propositions can be seen as equivalent to 𝟘
or 𝟙.

-  Contractible types ≃ 𝟙
-  Propositions ≃ (𝟘 if it’s not inhabited or 𝟙 if it’s inhabited)

Therefore, we will find a theorem later that says “if A is a
proposition, and it’s inhabited then it’s contractible”, and it makes
sense perfectly.

::

   hProp
     : ∀ (ℓ : Level) → Type (lsuc ℓ)

   hProp ℓ = ∑ (Type ℓ) isProp

In practice, we might want to say a type holds certain property and then
we can use the convenient following predicate.

::

   _has-property_
     : ∀ {ℓ : Level}
     → (A : Type ℓ)
     → (P : Type ℓ → hProp ℓ)
     → Type ℓ

   A has-property P = π₁ (P A)

   _holds-property = _has-property_

::

   _has-fun-property_
     : ∀ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁}{Y : Type ℓ₂}
     → (f : X → Y)
     → (P : ∀ {X : Type ℓ₁}{Y : Type ℓ₂} → (X → Y) → hProp (ℓ₁ ⊔ ℓ₂))
     → Type (ℓ₁ ⊔ ℓ₂)

   f has-fun-property P = π₁ (P f)

::

   _has-endo-property_
     : ∀ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁}
     → (f : X → X)
     → (P : ∀ {X : Type ℓ₁} → (X → X) → hProp ℓ₂)
     → Type ℓ₂

   f has-endo-property P = π₁ (P f)

Additionally, we may need to say, more explicity that two type share any
property whenever they are equivalent. Recall, these types do not need
to be in the same universe, however, for simplicity and to avoid dealing
with lifting types, we’ll assume they live in the same universe. Also,
we require a path, instead of the equivalence because at this point, we
have not define yet its type.

::

   _has-all-properties-of_because-of-≡_
       : ∀ {ℓ : Level}
       → (A : Type ℓ)
       → (B : Type ℓ)
       → A ≡ B
       -------------------------------------
       → (P : Type ℓ → hProp ℓ)
       → B has-property P → A has-property P

   A has-all-properties-of B because-of-≡ path
     = λ P BholdsP → tr (_has-property P) (! path) BholdsP
     where open import Transport

Now with (homotopy) propositional, we can consider the notion of
subtype, which is, just the ∑-type about the collection of terms that
holds some given property, we can use the following type ``sub-type``
for a proposition :math:`P : A → U` for some type :math:`A`. Assuming at
least there

::

   subtype
     : ∀ {ℓ : Level} {A : Type ℓ}
     → (P : A → hProp ℓ)
     → Type ℓ

   subtype P = ∑ (domain P) (π₁ ∘ P)

We prove now that the basic type (⊥, ⊤) are indeed (mere) propositions:

::

   ⊥-is-prop : ∀ {ℓ : Level} →  isProp (⊥ ℓ)
   ⊥-is-prop ()

::

   ⊤-is-prop : ∀ {ℓ : Level} →  isProp (⊤ ℓ)
   ⊤-is-prop _ _ = idp

More syntax:

::

   𝟘-is-prop = ⊥-is-prop
   𝟙-is-prop = ⊤-is-prop

Sets
~~~~

A type is a *set& by definition if any two equalities on the type are
equal Sets are types without any higher*\ dimensional structure*, all
parallel paths are homotopic and the homotopy is given by a continuous
function on the two paths.

::

   isSet
     : ∀ {ℓ : Level} → Type ℓ → Type ℓ
   isSet A = (x y : A) → isProp (x == y)

More syntax:

::

   _is-set = isSet

The type of sets

::

   hSet
     :  ∀ (ℓ : Level) → Type (lsuc ℓ)

   hSet ℓ = ∑ (Type ℓ) isSet

Groupoids
~~~~~~~~~

::

   isGroupoid
     : ∀ {ℓ : Level} → Type ℓ → Type ℓ

   isGroupoid A  = (a₀ a₁ : A) → isSet (a₀ ≡ a₁)

More syntax:

::

   _is-groupoid = isGroupoid

::

   Groupoid
     : ∀ (ℓ : Level) → Type (lsuc ℓ)

   Groupoid ℓ = ∑ (Type ℓ) isGroupoid

And, in case, we go a bit further, we have 2-groupoids. We can continue
define more h-levels for all natural numbers, however, we are not going
to use them.

::

   is-2-Groupoid
      : ∀ {ℓ : Level} → Type ℓ → Type ℓ

   is-2-Groupoid A  = (a₀ a₁ : A) → isGroupoid (a₀ ≡ a₁)

   is-2-groupoid = is-2-Groupoid
