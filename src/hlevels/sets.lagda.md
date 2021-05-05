---
title: "h-Levels: Sets"
description: "Examples of known types that are  propositions or sets"
---


--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module hlevels.sets where

open import level
open import mltt
open import function.core
open import function.homotopyequivalence
open import hlevels.core
open import homotopy.twocatconstructions.core
open import homotopy.twocatconstructions.ap2
open import homotopy.fibrations


open ≡-Reasoning
open ◾-lemmas
open transport-lemmas
```

### The empty type

The empty type is a proposition (not completely trivial) and hence a set.

```agda
𝟘-is-prop : is-prop 𝟘
𝟘-is-prop = λ x y → !𝟘 y

𝟘-is-set : is-set 𝟘
𝟘-is-set = prop→set 𝟘-is-prop
```
We can give a direct proof of the latter:

```agda
𝟘-is-set' : is-set 𝟘
𝟘-is-set' = λ x y p q → !𝟘 y
```

### The unit type

```agda
𝟙-is-contr : is-contr 𝟙
𝟙-is-contr = * , (𝟙-induction (_≡_ *) refl)

𝟙-is-prop : is-prop 𝟙
𝟙-is-prop = singleton→prop 𝟙-is-contr

𝟙-is-set : is-set 𝟙
𝟙-is-set = prop→set 𝟙-is-prop
```

Contractible types are isomorphic to `𝟙`, so we can prove the
"trivial" identity principle for `𝟙` from the HoTT book

```agda
iscontr-iso-𝟙 : ∀ {ℓ} {A : Set ℓ} → is-contr A → A ≅ 𝟙
iscontr-iso-𝟙 is = hoeq (λ _ → *)
                        (λ _ → center is)
                        (λ { * → refl})
                        (centrality is)

Id𝟙-is-𝟙 : {x y : 𝟙} → (x ≡ y) ≅ 𝟙
Id𝟙-is-𝟙 {x} {y} = iscontr-iso-𝟙 (is x y)
  where
    is : 𝟙 isofhlevel 1
    is = prop→hlevel1 𝟙-is-prop


Id𝟙-is-𝟙' : {x y : 𝟙} → (x ≡ y) ≅ 𝟙
Id𝟙-is-𝟙' = record { to = λ _ → *
                   ; from = λ _ → refl
                   ; ε = λ { * → refl}
                   ; η = λ { refl → refl}}
```

### Sum types {#sumtypes}

If `A` and `B` are sets, then so is their sum  `A ⊎ B`:

```agda
sum-isset : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → isSet A → isSet B → isSet (A ⊎ B)
sum-isset issetA issetB (inl a)  (inl a') p q = p ≡⟨ ap-inl-linv p ⁻¹ ⟩
                                                ap inl p' ≡⟨ ap2 inl α ⟩
                                                ap inl q' ≡⟨ ap-inl-linv q ⟩
                                                q ∎
  where
    -- any path between the injected elements in A ⊎ B comes from a
    -- path in A between the elements themselves
    inl-lc : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a a' : A}
             (p : _≡_ {A = A ⊎ B} (inl a) (inl a')) → a ≡ a'
    inl-lc refl = refl

    ap-inl-linv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a a' : A}
                  (p : _≡_ {A = A ⊎ B} (inl a) (inl a')) →
                  ap inl (inl-lc p) ≡ p
    ap-inl-linv refl = refl

    p' q' : a ≡ a'
    p' = inl-lc p
    q' = inl-lc q

    f = issetA

    α : p' ≡ q'
    α = f a  a' p' q'

sum-isset issetA issetB (inr b) (inr b') p q = p ≡⟨ ap-inr-linv p ⁻¹ ⟩
                                               ap inr p' ≡⟨ ap2 inr α ⟩
                                               ap inr q' ≡⟨ ap-inr-linv q ⟩
                                               q ∎
  where
    -- do the same for the right injection inr : B → A ⊎ B
    inr-lc : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {b b' : B}
             (q : _≡_ {A = A ⊎ B} (inr b) (inr b')) → b ≡ b'
    inr-lc refl = refl

    ap-inr-linv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {b b' : B}
                  (q : _≡_ {A = A ⊎ B} (inr b) (inr b')) →
                  ap inr (inr-lc q) ≡ q
    ap-inr-linv refl = refl

    p' q' : b ≡ b'
    p' = inr-lc p
    q' = inr-lc q

    g = issetB

    α : p' ≡ q'
    α = g b  b' p'  q'
```


### Σ-types {#sigma-types}

```agda
Σ-type-isset : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} → 
               isSet A → ((x : A) → isSet (P x)) → isSet (Σ A P)
Σ-type-isset {P = P} issetA issetP (x , s) (y , t) p  q = p  ≡⟨ γ ⟩
                                                                 q' ≡⟨ δ ⟩
                                                                 q ∎
             where
               pp qq : (x , s) ╝ (y , t)
               pp = PathΣ→PathPair p
               qq = PathΣ→PathPair q

               p₁ q₁ : x ≡ y
               p₁ = π₁ pp
               q₁ = π₁ qq

               -- the paths in the base are equal
               α : p₁ ≡ q₁
               α = issetA x y p₁ q₁

               -- in the fiber over y
               p₂ : transport P p₁ s ≡ t
               p₂ = π₂ pp

               q₂ : transport P q₁ s ≡ t
               q₂ = π₂ qq

               -- After breaking the paths with `PathPair`, we get different
               -- transports in the fiber over the endpoint of the path in the base.

               r : transport P p₁ s ≡ transport P q₁ s
               r = transport≡ α

               β : p₂ ≡ r ◾ q₂
               β = issetP y (transport P p₁ s) t p₂  (r ◾ q₂)

               qq' : (x , s) ╝ (y , t)
               qq' = p₁ , (r ◾ q₂)

               γγ : pp ≡ qq'
               γγ = pp ≡⟨ refl ⟩
                    (p₁ , p₂) ≡⟨ ap (λ v → p₁ , v) β ⟩
                    (p₁ , (r ◾ q₂)) ≡⟨ refl ⟩
                    qq' ∎

               q' : (x , s) ≡ (y , t)
               q' = PathPair→PathΣ qq'

               γ : p ≡ q'
               γ = p ≡⟨ (PathΣ-equiv {q = p}) ⁻¹ ⟩
                   PathPair→PathΣ pp ≡⟨ ap PathPair→PathΣ γγ ⟩
                   PathPair→PathΣ qq' ≡⟨ refl ⟩
                   q' ∎

               -- Move the path in the base and, accordingly, shift the corresponding
               -- path in the fiber:

               lemma : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {u v : Σ A P}
                       ((p , q) : u ╝ v) {p' : π₁ u ≡ π₁ v} (α : p ≡ p') →
                       (p , q) ≡ (p' , ((transport≡ α) ⁻¹ ◾ q))
               lemma (p , q) {.p} refl = refl

               δδ : qq' ≡ qq
               δδ = qq' ≡⟨ lemma qq' α ⟩
                    q₁ , (r ⁻¹ ◾ (r ◾ q₂)) ≡⟨ ap (λ v → (q₁ , v)) (assoc (r ⁻¹) r q₂) ⁻¹ ⟩
                    q₁ , ((r ⁻¹ ◾ r) ◾ q₂) ≡⟨ ap (λ v → (q₁ , v)) ((linv r) ◾ʳ q₂) ⟩
                    q₁ , (refl ◾ q₂) ≡⟨ refl ⟩
                    qq ∎

               δ : q' ≡ q
               δ = q' ≡⟨ refl ⟩
                   PathPair→PathΣ qq' ≡⟨ ap PathPair→PathΣ δδ ⟩
                   PathPair→PathΣ qq ≡⟨ PathΣ-equiv {q = q} ⟩
                   q ∎

Σ-type-is-set = Σ-type-isset
```

Simpler proof for the corresponding fact for propositions
```agda
Σ-type-isprop : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} → 
                isProp A → ((x : A) → isProp (P x)) → isProp (Σ A P)
Σ-type-isprop {P = P} ispa i u v = PathPair→PathΣ pp
  where
    pp : u ╝ v
    π₁ pp = (ispa (π₁ u) (π₁ v))
    π₂ pp = i (π₁ v) (transport P p (π₂ u)) (π₂ v)
      where
        p : π₁ u ≡ π₁ v
        p = ispa (π₁ u) (π₁ v)

Σ-type-is-prop = Σ-type-isprop
```

Cartesian product special case:

```agda
×-isset : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
           is-set A → is-set B → is-set (A × B)
×-isset ia ib = Σ-type-isset ia (λ _ → ib)

×-is-set = ×-isset


×-isprop : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
           isProp A → isProp B → isProp (A × B)
×-isprop ia ib = Σ-type-isprop ia (λ _ → ib)

×-is-prop = ×-isprop
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
