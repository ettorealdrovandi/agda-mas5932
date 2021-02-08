---
layout: page
title: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style"
chapter: 2
---

### Contents {#top}

1. [Universes](#universes)
1. [Finite Types](#finitetypes)
   1. [The Empty Type](#empty)
   1. [The One-Point Type](#onepoint)
   1. [Sum Types (Disjoint Union)](#sumtypes)
1. [Σ-Types](#sigma)
   1. [Cartesian Products](#cartesian)
   1. [Universal properties](#universal_cart_sigma)
1. [Π-Types](#pi)
   1. [Identity function and function composition](#functions)
   1. [Universal property for products and pullbacks](#pullback)
1. [Identity Types](#id)
   1. [Path Induction](#pathinduction)
   1. [Basic Operations with Identity Types](#basicop)
   1. [Reasoning with equality](#reasoning)
   1. [Lemmas](#lemmas)

--------------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module mltt where
```

### Universes {#universes}

```agda
open import level renaming (zero to lzero; suc to lsuc) public
```
For the future, define one more level
```agda
1ℓ : Level
1ℓ = lsuc 0ℓ
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Finite Types {#finitetypes}

#### The Empty Type {#empty}

```agda
open import mltt.empty public
```
<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>

#### The One-Point Type {#onepoint}

```agda
open import mltt.unit public
```
<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>


#### Sum Types (Disjoint Union) {#sumtypes}

```agda
open import mltt.sum public
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>


### Σ-Types {#sigma}

Σ-Types generalize arbitrary disjoint unions. If we have a base `B : Set ℓ` and a type family `(b : B) ⊢ E x : Set ℓ'`, we form the type `Σ B E` whose canonical elements are *pairs* $(b , e)$, where `b : B`, and `e : E b`. If the universe levels are different, `Σ B E : Set (ℓ ⊔ ℓ')`.

Instead of a `data` declaration of the form

    data Σ {ℓ ℓ'} (B : Set ℓ) (E : B → Set ℓ') : Set (ℓ ⊔ ℓ') where
      _,_ : (b : B) (e : E b) → Σ B E

we use a [`record`](https://agda.readthedocs.io/en/v2.6.1/language/record-types.html) type. Σ-Types can be translated into records, and viceversa, so we are not surrepticiously bringing unwanted features in the game. (An automatic translation is not available due to technical reasons.)

 The formation and introduction rules are:

```agda
--
record Σ {ℓ ℓ'} (B : Set ℓ) (E : B → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_ 
  field
    fst : B
    snd : E fst

infixr 50 _,_
```

Actually we do not need parentheses to write a pair—a canonical term of the Σ-type: we could simply write `b , e`: recall, in the definition of the constructor, the *body* of the function is an infix comma. However, it is often convenient to put the parentheses in for visual clarity.

For better compatibility with the mathematical notation $∑_{x ∈ A} E_x$ (where the sum means coproduct, that is $∐_{x ∈ A} E_x$) it is convenient to use a [`syntax`](https://agda.readthedocs.io/en/v2.6.1/language/syntax-declarations.html) declaration:

```agda
syntax Σ B (λ x → E) = Σ[ x ∈ B ] E
```

**Remark.** Defining the Σ-type as a record, we have a *named* access to the first and second components of a pair by way of the "field" part of the record declaration. Thus, if `u : Σ B E`, then:

1. Since Σ is a record, `Agda` will be able to (co)pattern match on the term `u` and
1. replace it with the pair `Σ.fst u , Σ.snd u`.

Thus the fields `fst` , `snd` act as projections. 

**Remark for Agda hackers.** Modules, and data type declarations, are *modules,* so `open public` them: this, for the Σ-type, would bring the names `fst` and `snd` in "scope": in this way, the pair corresponding to the term `u` would be `fst u , snd u`. We could have chosen names for the fields like `π₁` and `π₂`, that is, give a definition like

    record Σ {ℓ ℓ'} (B : Set ℓ) (E : B → Set ℓ') : Set (ℓ ⊔ ℓ') where
      constructor _,_ 
      field
        π₁ : B
        π₂ : E π₁

in which case the pair would simply be `π₁ , π₂`. This is very suggestive, but a bit confusing.

We will not usually open the module Σ and we will define the projections on their own as follows.

```agda
-- projection to the base
π₁ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} → Σ B E  → B
π₁ (b , e) = b

-- "projection" to the fiber
π₂ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} (t : Σ B E) → E (π₁ t)
π₂ (b , e) = e
```
As in many other cases, we can obtain the above expressions by just writing, say

    π₁ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} → Σ B E  → B
    π₁ u = {!!}

and using `C-c C-c` in Emacs to replace `u` with a pair. Then `C-c C-a` will fill in the hole automatically.

The **intuition** here is to imagine that if `(b : B) ⊢ E b` corresponds to a family $B ∋ b \mapsto E_b$ of spaces, then the Σ-type `Σ B E` corresponds to the *total space* $\coprod_{b ∈ B} E_b$ equipped with the projection
$$ \pi_1 \colon \coprod_{b ∈ B} E_b \to B$$
to the base


#### Induction and recursion for Σ-Types

The hardest is the type expression:

```agda
Σ-induction : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ} {E : B → Set ℓ'} {P : Σ B E → Set ℓ''} →
              ( (b : B) → (e : E b) → P (b , e) ) → 
              (u : Σ B E) → P u
```
whereas the proof is quite easy: write the hole

    Σ-induction g u = {!!}

and fill it in the usual way: `C-c C-c <var>` followed by `C-c C-a`
```agda
Σ-induction g (fst , snd) = g fst snd
```

Recursion is induction over a constant family, and we can, as usual, give both definitions
```agda
-- from induction
Σ-recursion : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ} {E : B → Set ℓ'} {P : Set ℓ''} →
              ( (b : B) → (e : E b) → P ) → Σ B E → P
Σ-recursion {P = P} = Σ-induction {P = (λ _ → P)}

-- direct definition
Σ-recursion' : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ} {E : B → Set ℓ'} {P : Set ℓ''} →
              ( (b : B) → (e : E b) → P ) → Σ B E → P
Σ-recursion' g (b , e) = g b e
```
As observed for sum types, of which Σ-types are a generalization, the recursion expresses the familiar universal property of coproducts. In sets (or other categories) if $\{ E_b \}_{b \in B}$ is a family of sets parametrized by $B$, and, say, $f_b \colon E_b \to P$ is a family of functions, then the universal property of coproducts says that there is a (unique) function
$f \colon \coprod_{b \in B} E_b \to P$, namely the one that to the pair $(b, e)$, where $e ∈ E_b$, assigns $f_b(e)$.

The `Σ-induction` is also referred to as <span style="color: teal">uncurry</span>, after [Haskell Curry](https://en.wikipedia.org/wiki/Haskell_Curry). There is an inverse:

```agda
curry : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ} {E : B → Set ℓ'} {P : Σ B E → Set ℓ''} →
        ( (u : Σ B E) → P u ) → 
        ( (b : B) → (e : E b) → P (b , e) )
curry f b e = f (b , e)
```
where a (dependent) function out of a Σ-type yields a two-variable function. (Note that the "uncurry" does exactly the opposite.)

#### Cartesian Products {#cartesian}

One very important special case is that of a Σ-type corresponding to a *non-dependent* function. That is just the **Cartesian Product**. This may seem unfamiliar at first glance, but if we have two, say, sets $A$ and $B$, then our familiar picture of $A × B$ as the set of pairs $(a,b)$ corresponds exactly to the non-symmetric view of the same as the disjoint union  of copies of $B$ parametrized by elements of $A$. This is precisely the Σ-type corresponding to the constant family `(a : A) ⊢ B`. Thus we just state:

```agda
-- non-dependent Σ-type = Cartesian product
_×_ : ∀{ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ') 
A × B = Σ A (λ x → B)
```
Note that in Agda $A$ and $B$ are allowed to be in different universes.

The Cartesian product will inherit the induction and recursion principles from those for the more general Σ-types. For instance:
```agda
×-induction : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {P : A × B → Set ℓ''} → 
               ((a : A) → (b : B) → P (a , b)) → (x : A × B) → P x
×-induction = Σ-induction 
```
but a direct definition is also possible
```agda
×-induction' : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {P : A × B → Set ℓ''} → 
               ((a : A) → (b : B) → P (a , b)) → (x : A × B) → P x
×-induction' g (a , b) = g a b
```

Since neither type is dependent, we can implement the standard swap of the factors in the Cartesian product:
```agda
×-swap : ∀ {ℓ ℓ'} {A : Set ℓ}{B : Set ℓ'} → A × B → B × A
×-swap (a , b) = b , a
```

```agda
×-assoc : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
    (A × B) × C → A × (B × C)
×-assoc (( a , b ) , c) = a , (b , c)
```
Once we have identity types, as an <span style="color: fuchsia">exercise</span> prove `×-assoc` and `×-swap` satisfy [Mac Lane's pentagonal and hexagonal diagrams](https://ncatlab.org/nlab/show/symmetric+monoidal+category) (plus certain additional higher diagrams).


#### Universal properties {#universal_cart_sigma}

We are used to think of the Cartesian product as a "product" in the categorical sense, in particular, the corresponding universal property involves a map *into* it, as opposed to one *out* of it, as it happens with the sum and the Σ-types. As we have seen, $A × B$, *when interpreted as* $\coprod_A B$, indeed behaves as a coproduct and we have observed how its induction principle reflects the corresponding universal property.

However, since by *construction* the canonical terms of `A × B` consist of pairs, we can prove that for any type `X` and `f : X → A` and `g : X → B` there is a (unique: this will be proved later) term of type `X → A × B`. Since we cannot yet prove the "uni" part, we call it "versal":
```agda
versal-cart : ∀ {ν ℓ ℓ'} {X : Set ν} {A : Set ℓ} {B : Set ℓ'}
              (f : X → A) (g : X → B) → X → (A × B)
versal-cart f g x = f x , g x
```

There is nothing special about the Cartesian product, and the same works for Σ-types. In other words, we can write the very same kind of "versal" property for the dependent sum type:
```agda
versal-Σ : ∀ {ν ℓ ℓ'} {X : Set ν} {B : Set ℓ} {E : B → Set ℓ'} →
          (f : X → B) → ((x : X) → E (f x)) → X → Σ B E
versal-Σ f g x = (f x) , (g x)
```
See [below](#pullback) for an interpretation. (Spoiler: this is a section of a pullback fibration.)

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Π-Types {#pi}

Π-Types are built-in in Agda, with the notation ∀. We are going to define an alternative name, for symmetry of exposition

```agda
Π : ∀ {ℓ ℓ'} (B : Set ℓ) (E : B → Set ℓ') → Set (ℓ ⊔ ℓ') 
Π B E = (x : B) → E x
```

This would probably not completely be in keeping with the form of MLTT we are sketching, where we need an explicit data declaration that expresses the *formation* and  *introduction* rules. The following does that (write Π′ in Emacs as `\Pi\'`) 
```agda
data Π′ {ℓ ℓ' : Level} (B : Set ℓ) (E : B → Set ℓ') : Set (ℓ ⊔ ℓ') where
  dfun : ((x : B) → E x) → Π′ B E
```
where we wrap the dependent function in a constructor called `dfun`. This is a bit impractical, in that we end up with essentially the same object wrapped up in an outer layer that will have to be stripped away in most applications.

Convenient syntax declarations:
```agda
syntax Π B (λ x → E) = Π[ x ∈ B ] E
syntax Π′ B (λ x → E) = Π′[ x ∈ B ] E
```
The standard function type `B → C` is just a particular case of a `Π`-type when the family `(x : B) ⊢ E x` is constant with value `C`.

The elimination rules are of course going to seem a bit tautological:
```agda
Π-elim : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} {b : B} → Π B E → E b
Π-elim {b = b} f = f b

Π′-elim : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} {b : B} → Π′ B E → E b
Π′-elim {b = b} (dfun f) = f b

-- Same thing, but sometimes more convenient
Π′-elim₁ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} → Π′ B E → (b : B) → E b 
Π′-elim₁ (dfun f) b = f b
```

In the analogy in which the Σ-type to `Σ [b : B] E b` is viewed as the total space of a fibration, the Π-type `Π [b : B] E b` ought to be the space of sections.

To define the latter:
```agda
Γ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} → Π B E → (B → Σ B E)
Γ f b = b , f b
```
Then we could prove that composing a section with the projection to the base is the identity operation

    gamma-is-sect: ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'}
                   (f : (b : B) → E b) → π₁ (Γ f b) ≡ b

for which we will need to introduce `≡` first. At that point it will be easy.

#### Identity and composition {#functions}

Since Π-types correspond to dependent functions, this is an appropriate place to introduce the identity function, and the function composition, copying them from the standard library. Let us use a *submodule* for this.

```agda
module function where
```
We are declaring some variables to avoid repetitions
```agda
  private
    variable
      ℓ ℓ' ℓ'' : Level
      A : Set ℓ
      B : Set ℓ'
      C : Set ℓ''
```
Then the identity function is the obvious one:
```agda
  -- identity function
  id : A → A
  id x = x
```
whereas for function composition we can define a dependent and a non-dependent version. We start with the first, and simply define the latter in terms of the former
```agda
  -- dependent composition
  infixr 9 _∘_
  _∘_ : ∀ {A : Set ℓ} {B : A → Set ℓ'} {C : {x : A} → B x → Set ℓ''} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

  -- non-dependent version (primed ′=\')
  infixr 9 _∘′_
  _∘′_ : (B → C) → (A → B) → (A → C)
  f ∘′ g = f ∘ g
```
Then we `open` the module to be able to use the naked names, in place of writing things like `function.id`.
```agda
open function public
```

This is also a good place to introduce certain convenience functions. Once again, let us encapsulate them in a module:

```agda
module convenience where
```
Trick to recover implicit arguments from functions without the need of giving them as arguments
```agda
  domain : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set ℓ
  domain {ℓ} {ℓ'} {A} {B} f = A

  codomain : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set ℓ'
  codomain {ℓ} {ℓ'} {A} {B} f = B
```
Evaluation maps are a standard thing
```agda
  ev' : ∀ {ℓ ℓ'} {A : Set ℓ} {E : A → Set ℓ'} (x : A) → ((x : A) → E x) → E x
  ev' x f = f x

  ev : ∀ {ℓ ℓ'} {A : Set ℓ} {E : A → Set ℓ'} → ((x : A) → E x) → (x : A) → E x
  ev f x = f x
```
This allows to recover the type of a term
```agda
  type-of : ∀{ℓ} {A : Set ℓ} → A → Set ℓ
  type-of {ℓ} {A} x = A
```
then, open the module to expose the names in it:
```agda
open convenience public
```

#### Universal property for products and pullbacks {#pullback}

The signature of `versal-Σ` above can be written in terms of function composition:
```agda
versal-Σ' : ∀ {ν ℓ ℓ'} {X : Set ν} {B : Set ℓ} {E : B → Set ℓ'} →
          (f : X → B) → ((x : X) → (E ∘ f) x) → X → Σ B E
versal-Σ' f g x = (f x) , (g x)
```
Typing `C-c C-n` (=normalize expression) in Emacs to bring up a dialog with Agda we can see that both `versal-Σ` and `versal-Σ'` normalize (i.e. they are computed to) the same canonical expression.

The type family `(x : X) ⊢ (E ∘ f) x` ought to be considered as giving rise to a fibration over `X`, namely the pullback of `(b : B) ⊢ E b` to `X`. Then the type `X → Σ B E` must be identified with that of sections of the pull back fibration, whose total space will be the Σ-type `Σ X (E ∘ f)`. First, there is an evident map of total spaces
```agda
map-over-total : ∀ {ν ℓ ℓ'} {X : Set ν} {B : Set ℓ} {E : B → Set ℓ'} →
       (f : X → B) → Σ X (E ∘ f) → Σ B E
map-over-total f (x , v) = (f x) , v
```
Second, we can compute the composition of this with the above defined `Γ`. We feed `Γ` the term `s : Π X (E ∘ f)` i.e `s : (x : X) ⊢ E (f x)` and apply `map-over-total` to it: 
```agda
map-section : ∀ {ν ℓ ℓ'} {X : Set ν} {B : Set ℓ} {E : B → Set ℓ'} →
      (f : X → B) → Π X (E ∘ f) → X → Σ B E
map-section {ν} {ℓ} {ℓ'} {X} {B} {E} f s = (map-over-total f) ∘ (Γ s)
```
If you calculate the normalization of this expression you will see that it is definitionally equal to `versal-Σ`.

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Identity Types {#id}

In Agda core, or in its Standard Library the identity type is defined as follows:
```agda
infix 4 _≡_  
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
```
It is common to use alternative names for the identity paths, such as
```agda
Id : {ℓ : Level} (A : Set ℓ) → A → A → Set ℓ
Id {ℓ} A = _≡_ {ℓ} {A}
```
as well as an explicit version of the reflexivity:
```agda
-- explicit version
idp : {ℓ : Level} {A : Set ℓ} (x : A) → x ≡ x
idp x = refl {x = x}
```
It is also common to see the name `paths` used in place of `≡`, owing to the topological interpretation. Notice as well that the notational convention about `=` (definitional equality) and `≡` (propositional equality) is opposite to that used in the HoTT book. 

It is convenient to be able to recover implicit arguments in equalities (identities) without mentioning them.
```agda
lhs : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → A
lhs {ℓ} {A} {x} {y} p = x

rhs : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → A
rhs {ℓ} {A} {x} {y} p = y
```
The idea is to be able to write `lhs p` to refer to `x` above.

Note that the identity type is a genuine *family* indexed by the terms of a given type.

#### Path induction {#pathinduction}

The induction principle for the identity types, often called path induction, is given by Martin-Löf in the following form
```agda
≡-induction : ∀ {ℓ ℓ'} {A : Set ℓ} (D : (x y : A) → x ≡ y → Set ℓ') →
              ((x : A) → D x x refl) → ( (x y : A) → (p : x ≡ y) → D x y p )
```
The proof is by computation of `p : x ≡ y` to the canonical term `refl : x ≡ x`. Interactively, we have

    ≡-induction D d x y p = {!!}

Then, we can do a case splitting (with `C-c C-c` in Emacs) on `p` which yields

    ≡-induction D d x .x refl = {!!}

which is filled automatically by Agda:
```agda
≡-induction D d x .x refl = d x
```
The oddly looking `.x`, what Agda calls an "irrefutable pattern," also "dot-pattern," is due to the following: if `p=refl` (definitionally) then `y=x` (again definitionally). Agda signals this fact by pre-pending a dot; `.x` means that the expression is there to only satisfy the type-checking process.

In keeping with Martin-Löf own notation we call this `𝕁`
```agda
𝕁 = ≡-induction
```
<!--
There is a commonly used "pointed" variant of `𝕁`, called "based path induction" in the HoTT book, where we isolate one of the two terms in the type:
```agda-ignore
ℍ : ∀ {ℓ ℓ'} {A : Set ℓ} (x : A) (C : (y : A) → x ≡ y → Set ℓ') → 
    C x refl → (y : A) → (p : x ≡ y) → C y p
ℍ x C c .x refl = c
```
These two versions agree. First, we can obtain `𝕁` from `ℍ` in the following way
```agda-ignore
-- Standard path induction from the based one
𝕁' : ∀ {ℓ ℓ'} {A : Set ℓ} (D : (x y : A) → x ≡ y → Set ℓ') → 
     ((x : A) → D x x refl) → (x y : A) → (p : x ≡ y) → D x y p
𝕁' D d x y p = ℍ x (D x) (d x) y p
-- 𝕁' D d x = ℍ x (D x) (d x)
```
Then check that `𝕁` and `𝕁'` agree:
```agda-ignore
𝕁-to-𝕁' : ∀ {ℓ ℓ'} {A : Set ℓ} (D : (x y : A) → x ≡ y → Set ℓ')  
          (d : (x : A) → D x x refl) (x y : A) (p : x ≡ y) →
          𝕁 D d x y p ≡ 𝕁' D d x y p
```
if we put a hole and simply case-split (`C-c C-c`) on `p` we get

    𝕁-to-𝕁' D d x .x refl = {!!}

If we normalize (`C-u C-u C-c C-,`) the goal, Agda shows that we must prove `d x ≡ d x`, a case for filling the hole with `refl`:
```agda-ignore
𝕁-to-𝕁' D d x .x refl = idp (d x) -- signal which reflexivity with an explicit term
```

Conversely, we can define the based path induction from the standard one without using pattern matching on `p`. This is considerably *harder*
```agda-ignore
ℍ' : ∀ {ℓ ℓ'} {A : Set ℓ} (x : A) (C : (y : A) → x ≡ y → Set ℓ') → C x refl →
     (y : A) → (p : x ≡ y) → C y p
ℍ' {ℓ} {ℓ'} {A} x C c y p = 𝕁 𝔻 (λ x C c → c) x y p C c where 
  𝔻 : ∀ {ℓ ℓ'} {A : Set ℓ} → (x y : A) → (p : x ≡ y) → Set (ℓ ⊔ lsuc ℓ')
  𝔻 {ℓ} {ℓ'} {A} x y p = (C : ((y' : A) → (p' : x ≡ y') → Set ℓ')) → (C x refl → C y p)
```
-->

#### Basic Operations with Identity Types {#basicop}

We will refer to terms of an identity type as "identifications." Thus, if `p : x ≡ y`, then we will refer to `p` as an identification of `x` with `y`. Of course, owing to the upcoming homotopical interpretation, we will also refer to `p` as a "path" from `x` to `y`.

Once we have the induction principle for the identity types, we can immediately define certain basic operations with them:

  1. [*transport*](#transport) along an identification,
  1. [*application*](#ap) of a function to an identification, and
  1. [*composition* and *inversion*](#composition) of identifications.

More operations that flesh out the homotopical interpretation will be defined later. There are also lemmas that govern these operations and how they interact. These lemmas, proved below, give meaning to the slogan "Types are higher groupoids."

##### Transport {#transport}

If `P : A → Set ℓ` is a dependent type, the `transport` along `p : x ≡ y` results in a map `P x → P y`. This is the analog of the (parallel) transport along a path in the base of a fibration. We are going to provide two proofs of if. First, the harder inductive one using the `𝕁`-induction principle.
```agda
transport𝕁 : ∀{ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A}
            (p : x ≡ y) → P x → P y
transport𝕁 {ℓ} {ℓ'} {A} P {x} {y} p = 𝕁 D d x y p 
  where
    D : ∀{ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (x y : A) → x ≡ y → Set ℓ'
    D {P = P} x y p = P x → P y
    d : ∀{ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (x : A) → D {P = P} x x refl
    d x = id
```
In the above, we used the `where` keyword: [check it out](https://agda.readthedocs.io/en/v2.6.1/language/let-and-where.html?highlight=where#where-blocks). This gets easier if we pattern-match on `p`:
```agda
transport : ∀{ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A}
            (p : x ≡ y) → P x → P y
transport P refl = id
```
Of course the two versions agree, in the following sense
```agda
transport-agreement : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (p : x ≡ y) →
                      transport P p ≡ transport𝕁 P p
transport-agreement P refl = idp (id)
```

##### Applicative {#ap}

If we have an identification `p : x ≡ y`, where `x y : A`, and `f : A → B`, then we can inquire about the "image" of the path in `B` under the mapping `f`, in other words, that we get a path `ap f p : f x ≡ f y` between the images. Again, this can be done in two ways; by pattern matching:

```agda
ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) → 
     x ≡ y → f x ≡ f y
ap f refl = refl
```
and with path induction:
```agda
ap𝕁 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) →
      x ≡ y → f x ≡ f y
ap𝕁 {ℓ} {ℓ'} {A} {B} {x} {y} f p = 𝕁 D d x y p where
  D : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (x y : A) (p : x ≡ y) → Set ℓ'
  D {f = f} x y p = f x ≡ f y
  d : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (x : A) → D {f = f} x x refl
  d x = refl
```
There is a dependent variant of `ap`, `apd`, which we will define later. For now, we check that the two versions we have just defined agree:
```agda
ap-agreement : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) (p : x ≡ y) → ap f p ≡ ap𝕁 f p
ap-agreement f refl = idp refl
```

##### Composition and inversion of identifications {#composition}

This is one of the most interesting parts. Composition and inversion of identifications tie the formalism of equality as an equivalence relation with the intuition that paths in a space form a (higher) groupoid.

We start from the *inversion*. First, the induction version:
```agda
≡-inv𝕁 : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
≡-inv𝕁 {ℓ} {A} {x} {y} p = 𝕁 (λ x y p → y ≡ x) (λ x → refl) x y p
```
And of course we have another proof based on pattern matching on the constructor
```agda
infixr 30 _⁻¹
_⁻¹ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl
```
The postfix notation was chosen to reflect that fact that this is the construction of the *inverse path* in homotopy theory. For symmetry:
```agda
≡-inv = _⁻¹
```
As for *composition*, this is the composition of two successive identifications, the intuition behind it being that this operation should correspond to path concatenation in topology. As usual, following the HoTT book, we begin with a proof of the composition operation via path induction:
```agda
≡-comp𝕁 : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y ) → y ≡ z → x ≡ z
≡-comp𝕁 {ℓ} {A} {x} {y} {z} p = 𝕁 D d x y p z where 
    D : ∀ {ℓ} {A : Set ℓ} (x y : A) (p : x ≡ y) → Set ℓ
    D {ℓ} {A} x y p = (z : A) → (q : y ≡ z) → x ≡ z

    d : ∀ {ℓ} {A : Set ℓ} (x : A) → D x x refl -- Π[ z ∈ A ] Π[ q ∈ x ≡ z ] (x ≡ z)
    d {ℓ} {A} x z q = 𝕁 E (λ x → refl) x z q where
        E : ∀ {ℓ} {A : Set ℓ} → Π[ x ∈ A ] Π[ z ∈ A ] Π[ q ∈ x ≡ z ] Set ℓ
        E {ℓ} {A} x z q = x ≡ z
```
A second proof (this is also in the HoTT book) uses the induction or pattern matching on one of the constructors.
```agda
infix 25 _◾_
_◾_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
refl ◾ q = q
```
<span style="color: teal; font-weight: bold">Remark</span> Note how, from the induction principle,  we have **proved** both the *symmetric* and *transitive* properties of propositional equality.

<span style="color: teal; font-weight: bold">Remark</span> Note that the path composition is in *lexicographical order,* not in the standard function-theoretic one.

Note how the proof of `_◾_` is asymmetric. We can always define the same operation with a different proof
```agda
_◾′_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
p ◾′ refl = p
```
Of course we should give a proof they agree:
```
◾-agreement : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ◾ q ≡ p ◾′ q
◾-agreement refl refl = refl
```


#### Reasoning with equality {#reasoning}

One drawback of writing proofs in Agda is that, say, pattern-matching destroys the "history" of the proof and only leaves the final result, whereas it would be beneficial to be able to record the *steps* we make in a chain of deductions—pretty much in the same way as we would while writing proofs on paper.

There is a lovely technique, used in many spots in the Agda Standard Library, for example, which provides for recording the *reason* as to why some inference holds. It allows to use a chain of deductions based on  propositional equality `≡`.

We reimplement it from scratch here:

```agda
module ≡-Reasoning {ℓ : Level} {A : Set ℓ}  where

  infix 3 _∎
  infixr 2 _≡⟨_⟩_
  
  _≡⟨_⟩_ : (x : A) {y z : A} →
           x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = p ◾ q

  _∎ : (x : A) → x ≡ x
  x ∎ = idp x
```
`_◾` is a postfix function assigning to a term `x : A` its reflexivity term in `x ≡ x`. The other, `_≡⟨_⟩_`, is a modified version of transitivity.

What these two functions do is to allow this form of writing:

    x ≡⟨ p ⟩ 
    y ≡⟨ q ⟩
    z ∎ 

We are going to see instances of `≡-Reasoning` at work in lemmas about `transport`, `ap`, and `_◾_`.


#### Some lemmas {#lemmas}

First, let us establish the usual identities, that is, those familiar from Topology, for path operations.

```agda
-- Lemmas about _◾_ (path composition)

module ◾-lemmas where

  private
    variable
      ℓ : Level
      A : Set ℓ
      x y : A

  -- refl is a left-unit
  lu : (p : x ≡ y) → idp (lhs p) ◾ p ≡ p
  lu p = idp p

  -- refl is a right-unit
  ru : (p : x ≡ y) → p ◾ idp (rhs p) ≡ p
  ru refl = refl

  lu=ru : {x : A} → lu (idp x) ≡ ru (idp x)
  lu=ru = idp (refl)

  -- right inverse
  rinv : (p : x ≡ y) → p ◾ p ⁻¹ ≡ idp (lhs p)
  rinv refl = refl

  -- left inverse
  linv : (p : x ≡ y) → p ⁻¹ ◾ p ≡ idp (rhs p)
  linv refl = refl

  -- taking the inverse twice is the identity
  inv²-id : (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
  inv²-id {x = x} refl = idp (refl {x = x})

  -- composition is associative
  assoc : {z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ◾ q) ◾ r ≡ p ◾ (q ◾ r)
  assoc refl q r = idp (q ◾ r)
```
One should be aware that the proof of associativity produces a term of a certain identity type, namely `(p ◾ q) ◾ r ≡ p ◾ (q ◾ r)`. Both the left and right hand side are identifications of `x` with `z` as terms of `A`. In turn, the witness of the associativity will satisfy higher identities (pentagons and up).

<span style="color: fuchsia">Exercise.</span> Define functions with the following type signatures

      assoc𝕁 : assoc𝕁 : {x y z w : A} (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → (p ◾ q) ◾ r ≡ p ◾ (q ◾ r)
      assoc𝕁 = {!!}

      inv²-id𝕁 : {x y : A} (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
      inv²-id𝕁 = {!!}

where you prove the same statements using Martin-Löf's 𝕁-induction, instead of pattern matching on the variables. (The proofs in the 𝕁-style can be found in the HoTT book.)

The operation `ap` maps a path via a function. Thus we expect it to have certain functorial properties relative to the path operations, which we prove in the following module:
```agda
module ap-lemmas where

  private
    variable
      ℓ ℓ' ℓ'' : Level
      A : Set ℓ
      B : Set ℓ'
      C : Set ℓ''
      x y z : A

  open ◾-lemmas

  ap◾ : (f : A → B) (p : x ≡ y) (q : y ≡ z) → ap f (p ◾ q) ≡ (ap f p) ◾ (ap f q)
  ap◾ f refl q = idp (ap f q)

  -- destruct q
  -- use reasoning
  ap◾' : (f : A → B) (p : x ≡ y) (q : y ≡ z) → ap f (p ◾ q) ≡ (ap f p) ◾ (ap f q)
  ap◾' f p refl = ap f (p ◾ refl) ≡⟨ ap (ap f) (ru p) ⟩
                  ap f p ≡⟨ ru (ap f p) ⁻¹ ⟩
                  (ap f p) ◾ refl ∎
    where
      open ≡-Reasoning

  ap◾′ : (f : A → B) (p : x ≡ y) (q : y ≡ z) → ap f (p ◾′ q) ≡ (ap f p) ◾′ (ap f q)
  ap◾′ f p refl = idp (ap f p)

  ap⁻¹ : (f : A → B) (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
  ap⁻¹ f refl = refl

  ap∘ : (f : A → B) (g : B → C) (p : x ≡ y) →
        ap (g ∘′ f ) p ≡ ap g (ap f p)
  ap∘ f g refl = refl

  apid : (p : x ≡ y) → ap id p ≡ p
  apid refl = refl

  apconst : (p : x ≡ y) (b : B) → ap (λ (x : A) → b) p ≡ refl
  apconst refl b = refl

```

We have a similar situation with the transport operation. If `P : A → Set ℓ'`, the operation `transport` assigns to an identification `p : x ≡ y` in the base type a function `P x → P y`. In the following modules we study some of its properties relative to path and function composition.
```agda
module transport-lemmas where

  private
    variable
      ℓ ℓ' : Level
      A : Set ℓ
      P : A → Set ℓ'

  -- transport is compatible with path composition
  transport◾ : {x y z : A} (p : x ≡ y) (q : y ≡ z) {u : P x} → 
               ( (transport P q) ∘′ (transport P p) ) u ≡ transport P (p ◾ q) u
  transport◾ refl q = refl

  -- transport is compatible with function composition
  transport∘ : ∀{ν} {X : Set ν} {x y : X} {f : X → A} 
               (p : x ≡ y) {u : P (f x)} → transport (P ∘′ f) p u ≡ transport P (ap f p) u
  transport∘ refl = refl

  -- transport is compatible with morphisms of fibrations (f : Π[ x ∈ A ] (P x → Q x))
  transport-cov : ∀ {ℓ''} {Q : A → Set ℓ''} {x y : A} {f : (x : A) → P x → Q x}
                   (p : x ≡ y) {u : P x} → transport Q p (f x u) ≡ f y (transport P p u)
  transport-cov {x = x} {f = f} refl {u} = idp (f x u)

  -- state transport-cov without the u : P x
  transport-cov' : ∀ {ℓ''} {Q : A → Set ℓ''} {x y : A} {f : (x : A) → P x → Q x}
                   (p : x ≡ y) → transport Q p ∘ (f x) ≡ (f y) ∘ (transport P p)
  transport-cov' refl = refl

  -- compatibility with identifications of path
  transport≡ : {x y : A} {p q : x ≡ y} (α : p ≡ q) {u : P x} →
              transport P p u ≡ transport P q u
  transport≡ refl = refl
```

A useful special case is that of transport in a family of identity types. Namely `P : A → Set ℓ'` where `P x` is a type of paths, perhaps in `A` itself, which is the simplest case to consider.

```agda
module transport-in-paths where

  private
    variable
      ℓ : Level
      A : Set ℓ

  open ◾-lemmas

  transport-path-f : {a x y : A} (p : x ≡ y) (q : a ≡ x) →  
                     transport (λ v → a ≡ v) p q ≡ q ◾ p
  transport-path-f refl q = ru q ⁻¹

  transport-path-b : {a x y : A} (p : x ≡ y) (q : x ≡ a) →
                     transport (λ v → v ≡ a) p q ≡ p ⁻¹ ◾ q
  transport-path-b refl q = refl

  transport-path-id : {x y : A} (p : x ≡ y) (q : x ≡ x) →
                      transport (λ v → v ≡ v) p q ≡ (p ⁻¹ ◾ q) ◾ p
  transport-path-id refl q = ru q ⁻¹

  transport-path-id' : {x y : A} (p : x ≡ y) (q : x ≡ x) →
                       transport (λ v → v ≡ v) p q ≡ p ⁻¹ ◾ (q ◾ p)
  transport-path-id' refl q = ru q ⁻¹

  transport-path-parallel : ∀ {ℓ'} {B : Set ℓ'} {f g : A → B} {x y : A}
                            (p : x ≡ y) (q : f x ≡ g x) →
                            transport (λ v → f v ≡ g v) p q ≡ ((ap f p) ⁻¹ ◾ q) ◾ (ap g p)
  transport-path-parallel refl q = ru q ⁻¹

  transport-path-parallel' : ∀ {ℓ'} {B : Set ℓ'} {f g : A → B} {x y : A}
                             (p : x ≡ y) (q : f x ≡ g x) →
                             transport (λ v → f v ≡ g v) p q ≡ (ap f p) ⁻¹ ◾ (q ◾ ap g p)
  transport-path-parallel' refl q = ru q ⁻¹

  transport-path-fun-left : ∀ {ℓ'} {B : Set ℓ'} {f : A → B} {b : B} {x y : A}
                            (p : x ≡ y) (q : f x ≡ b) →
                            transport (λ v → f v ≡ b) p q ≡ (ap f p) ⁻¹ ◾ q
  transport-path-fun-left refl q = refl

  transport-path-fun-right : ∀ {ℓ'} {B : Set ℓ'} {b : B} {g : A → B} {x y : A}
                            (p : x ≡ y) (q : b ≡ g x) →
                            transport (λ v → b ≡ g v) p q ≡  q ◾ ap g p
  transport-path-fun-right refl q = ru q ⁻¹

```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
