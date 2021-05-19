---
title: "Fibrations"
description: "Dependent types as fibrations"
---


### Contents {#top}

1. [Path lifting](#pathlift)
   1. [Naive path lifting](#naive)
   1. [PathPair](#pathpair)
   1. [PathOver](#pathover)

1. [Homotopy fibers](#hfib)
--------------------------------------------------

One of the fundamental interpretations of HoTT is that type families, i.e. dependent types are interpreted as fibrations. In turn, the defining property of  a fibration in a homotopy theory is the lifting one with respect to certain class of maps, in particular paths.

We prove that this is the case in a minimal type theory: we show, mostly following the HoTT book, that a dependent type `P : A → Set ℓ'` has such a notion of path lifting. 


```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.fibrations where

open import mltt
open import function

open ≡-Reasoning
open ◾-lemmas
open ap-lemmas
open transport-lemmas
```

### Path lifting {#pathlift}

#### Naive path lifting {#naive}

```agda
-- naive version of pathlift
pathlift : ∀{ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} {u : P x} (p : x ≡ y) →
           x , u ≡ y , (transport P p u)
pathlift {ℓ} {ℓ'} {A} {P} {x} {.x} {u} refl = idp (x , u)

-- this shows that pathlift projects back to the identity of x ≡ y
pathlift-covers-path : ∀{ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} {u : P x} (p : x ≡ y) →
                       ap π₁ (pathlift {P = P} {u = u} p) ≡ p
pathlift-covers-path {ℓ} {ℓ'} {A} {P} {x} {.x} {u} refl = refl
```

```agda
-- global section
Γ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} → Π B E → (B → Σ B E)
Γ f b = b , f b

global = Γ
```

Now, if `f : Π A P`, applying `Γ f` to an identification `p : x ≡ y` in the base gives a path in the total space, so one can consider `ap (Γ f) p` as a lift to the total space.

```agda
apd-naive : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} (f : Π[ x ∈ A ] P x) → 
            x ≡ y → (global f) x ≡ (global f) y
apd-naive f p = ap (global f) p 
```

which of course maps down to the base to a path (propositionally) equal to `p`, that is, `apd-naive` is a form of pathlift:

```agda
apd-naive-pathlift : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} {p : x ≡ y}
                     (f : Π[ x ∈ A ] P x) → ap π₁ (apd-naive f p) ≡ p
apd-naive-pathlift {p = p} f = ap π₁ (apd-naive f p) ≡⟨  (ap∘ (global f) π₁ p) ⁻¹ ⟩
                               ap (π₁ ∘′ (global f)) p ≡⟨  apid p ⟩
                               p ∎
```

#### PathPair {#pathpair}

If `P : A → Set ℓ'` is a dependent type, **PathPair**  constructs the fibration whose base consists of paths in `A` and whose fibers consist of *vertical identity types* in the fibers of the terminal points:

```agda
PathPair : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (u v : Σ A P) → Set (ℓ ⊔ ℓ')
PathPair {P = P} u v = Σ[ p ∈ (π₁ u ≡ π₁ v) ] ( transport P p (π₂ u) ≡ (π₂ v) )

infix 30 PathPair
syntax PathPair u v = u ╝ v
```

The dependent `apd` is a section:

```agda
apd-is-section : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f : Π[ x ∈ A ] P x) {x y : A} → 
                 x ≡ y → (x , f x) ╝ (y , f y)
apd-is-section f = global (apd f)

```
In fact the types `u ≡ v` and `u ╝ v` are isomorphic:

```agda
pathinfiber : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P}
              (q : u ≡ v) → transport P (ap π₁ q) (π₂ u) ≡ π₂ v
pathinfiber {u = u} refl = idp (π₂ u)

PathPair→PathΣ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P} →
                 u ╝ v → u ≡ v
PathPair→PathΣ {u = x , s} {v = .x , t} (refl , q) = ap (λ _ → x , _) q

PathΣ→PathPair : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P} →
                 u ≡ v → u ╝ v
PathΣ→PathPair {u = u} {v = v} q = (ap π₁ q) , pathinfiber q

PathΣ-equiv : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P} {q : u ≡ v} →
                PathPair→PathΣ (PathΣ→PathPair q) ≡ q
PathΣ-equiv {q = refl} = idp (refl)

PathPair-equiv : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P} {q : u ╝ v} →
                PathΣ→PathPair (PathPair→PathΣ q) ≡ q
PathPair-equiv {u = u} {.(π₁ u) , .(π₂ u)} {q = refl , refl} = refl

PathΣ-iso-PathPair : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P} →
                     (u ≡ v) ≅ (u ╝ v)
PathΣ-iso-PathPair = record { to = PathΣ→PathPair
                            ; from = PathPair→PathΣ
                            ; ε = λ q → PathPair-equiv
                            ; η = λ q → PathΣ-equiv }
```

#### Cartesian products {#cartesian}

We could adapt `PathPair` to cartesian products, but we can establish the identity principle directly. 

```agda
ap-pair : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {u v : A × B} →
          u ≡ v → ((π₁ u ≡ π₁ v) × (π₂ u ≡ π₂ v))
ap-pair = λ p → ap π₁ p , ap π₂ p

pair⁼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {u v : A × B} →
        ((π₁ u ≡ π₁ v) × (π₂ u ≡ π₂ v)) → u ≡ v
pair⁼ = λ { (refl , refl) → refl}

cart-id-princ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (u v : A × B) →
                (u ≡ v) ≅ ((π₁ u ≡ π₁ v) × (π₂ u ≡ π₂ v))
cart-id-princ u v = record { to =  ap-pair
                           ; from = pair⁼ 
                           ; ε = λ { (refl , refl) → refl}
                           ; η = λ { refl → refl} }
```

#### PathOver {#pathover}

See "Foundations" in [UniMath](https://github.com/UniMath/UniMath) library. 

To a path `p : x ≡ y` and terms `s : P x` and `t : P y` we  assign the type of paths from `u` to `v` lying "over" `p`.

```agda
PathOver : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (p : x ≡ y) (s : P x) (t : P y) → Set ℓ'
PathOver P refl s t = s ≡ t

infix 30 PathOver
syntax PathOver P p s t = s ≡[ P ↓ p ] t


PathOver→PathPair : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} (p : x ≡ y) (s : P x) (t : P y) →
                    s ≡[ P ↓ p ] t → (x , s) ╝ (y , t)
PathOver→PathPair {P = P} refl s t q = refl , q

PathPair→PathOver : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P }
                    (q : u ╝ v) → (π₂ u) ≡[ P ↓ (π₁ q) ] (π₂ v)
PathPair→PathOver (refl , q~) = q~

PathOver→PathΣ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} (p : x ≡ y) (s : P x) (t : P y) →
                     s ≡[ P ↓ p ] t → (x , s) ≡ (y , t)
PathOver→PathΣ {P = P} p s t = PathPair→PathΣ ∘′ (PathOver→PathPair p s t)

PathΣ→PathOver : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P} (q : u ≡ v) → 
                 (π₂ u) ≡[ P ↓ (ap π₁ q) ] (π₂ v)
PathΣ→PathOver q = PathPair→PathOver ( (PathΣ→PathPair q) )
```

### Homotopy fibers {#hfib}

The homotopy fiber construction allows to replace any map with a fibration.

```agda
hfib : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (b : B) → Set (ℓ ⊔ ℓ')
hfib f b = Σ[ a ∈ domain f ] ((f a) ≡ b)

syntax hfib f b = f ⁻¹ b

-- extracting the components
hfib-pt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {b : B} → 
                   hfib f b → A
hfib-pt = π₁

hfib-path : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {b : B} → 
            (u : hfib f b) → f (hfib-pt u) ≡ b
hfib-path = π₂
```

Pointwise homotopies preserve homotopy fibers:

```agda
pointwise-homot-hfib-iso : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → 
                         (f ~ g) → (b : B) → hfib f b ≅ hfib g b
pointwise-homot-hfib-iso {ℓ} {ℓ'} {A} {B} {f} {g} h b = hoeq k k⁻¹ ε η

  where
    open import homotopy.twocatconstructions

    k : hfib f b → hfib g b
    k = λ { (a , p) → a , ((h a) ⁻¹ ◾ p)}

    k⁻¹ : hfib g b → hfib f b
    k⁻¹ (a , q) = a , ((h a) ◾ q)

    η : k⁻¹ ∘′ k ~ id
    η (a , p)  = ap (λ v → (a , v)) γ
      where
        γ : (h a ◾ (h a ⁻¹ ◾ p)) ≡ p
        γ = (h a ◾ (h a ⁻¹ ◾ p)) ≡⟨ (assoc (h a) (h a ⁻¹) p ) ⁻¹ ⟩
            ((h a ◾ h a ⁻¹) ◾ p) ≡⟨ rinv (h a) ◾ʳ p ⟩
            p ∎
        
    ε : k ∘′ k⁻¹ ~ id
    ε (a , q) = ap (λ v → (a , v)) γ
      where
        γ : (h a ⁻¹ ◾ (h a ◾ q)) ≡ q
        γ = (h a ⁻¹ ◾ (h a ◾ q)) ≡⟨ ( assoc (h a ⁻¹) (h a) q ) ⁻¹ ⟩
            ((h a ⁻¹ ◾ h a) ◾ q) ≡⟨ linv (h a) ◾ʳ q ⟩
            q ∎
```
