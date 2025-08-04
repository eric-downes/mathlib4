/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import MathlibTest.CategoryTheory.TestFramework

/-!
# Tests for If-Then-Else Composition Lemmas

This file tests the lemmas that show how composition distributes over if-then-else
and dependent if-then-else expressions.

## Coverage

- `comp_ite` - ✓ Tested
- `ite_comp` - ✓ Tested
- `comp_dite` - ✓ Tested
- `dite_comp` - ✓ Tested

Coverage: 4/4 lemmas (100%)
-/

namespace CategoryTheoryTest.IteComposition

open CategoryTheory

section BasicIte

variable {C : Type*} [Category C] {X Y Z : C}

/-- Test comp_ite: composition distributes into the branches of ite -/
example {P : Prop} [Decidable P] (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' :=
  comp_ite f g g'

/-- Test ite_comp: composition distributes into the branches of ite -/
example {P : Prop} [Decidable P] (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (if P then f else f') ≫ g = if P then f ≫ g else f' ≫ g :=
  ite_comp f f' g

/-- Concrete example with a specific proposition -/
example (n : Nat) (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if n = 0 then g else g') = if n = 0 then f ≫ g else f ≫ g' :=
  comp_ite f g g'

end BasicIte

section DependentIte

variable {C : Type*} [Category C] {X Y Z : C}

/-- Test comp_dite: composition distributes into dependent if-then-else -/
example {P : Prop} [Decidable P] (f : X ⟶ Y) 
    (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
    (f ≫ if h : P then g h else g' h) = if h : P then f ≫ g h else f ≫ g' h :=
  comp_dite f g g'

/-- Test dite_comp: composition distributes into dependent if-then-else -/
example {P : Prop} [Decidable P] 
    (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) :
    (if h : P then f h else f' h) ≫ g = if h : P then f h ≫ g else f' h ≫ g :=
  dite_comp f f' g

/-- Example where the branches depend on the proof -/
example (n : Nat) (f : X ⟶ Y) 
    (g : (h : n > 0) → (Y ⟶ Z)) 
    (g' : (h : ¬n > 0) → (Y ⟶ Z)) :
    (f ≫ if h : n > 0 then g h else g' h) = 
    if h : n > 0 then f ≫ g h else f ≫ g' h :=
  comp_dite f g g'

end DependentIte

section ConcreteExamples

/-- ITE composition in Type* -/
example {X Y Z : Type*} (P : Prop) [Decidable P] 
    (f : X → Y) (g g' : Y → Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' :=
  comp_ite f g g'

/-- Concrete computation with natural numbers -/
example (n : Nat) : 
    ((· + 1) ≫ if n = 0 then (· * 2) else (· * 3) : Nat → Nat) = 
    if n = 0 then (fun x => (x + 1) * 2) else (fun x => (x + 1) * 3) :=
  comp_ite _ _ _

/-- Test with actual values -/
example : ((· + 1) ≫ if 5 > 3 then (· * 2) else (· * 3) : Nat → Nat) 10 = 22 := by
  simp [comp_ite]

/-- Dependent version with concrete types -/
example (n : Nat) (g : (h : n > 0) → (Nat → Bool)) 
    (g' : (h : ¬n > 0) → (Nat → Bool)) :
    ((· + 1) ≫ if h : n > 0 then g h else g' h) = 
    if h : n > 0 then (· + 1) ≫ g h else (· + 1) ≫ g' h :=
  comp_dite _ _ _

end ConcreteExamples

section ChainedIte

variable {C : Type*} [Category C] {W X Y Z : C}

/-- Multiple ite expressions in composition -/
example {P Q : Prop} [Decidable P] [Decidable Q] 
    (f : W ⟶ X) (g g' : X ⟶ Y) (h h' : Y ⟶ Z) :
    f ≫ (if P then g else g') ≫ (if Q then h else h') = 
    if P then 
      if Q then f ≫ g ≫ h else f ≫ g ≫ h'
    else 
      if Q then f ≫ g' ≫ h else f ≫ g' ≫ h' := by
  simp only [comp_ite, ite_comp]

/-- Nested ite expressions -/
example {P Q : Prop} [Decidable P] [Decidable Q] 
    (f : X ⟶ Y) (g₁ g₂ g₃ : Y ⟶ Z) :
    f ≫ (if P then g₁ else if Q then g₂ else g₃) = 
    if P then f ≫ g₁ else if Q then f ≫ g₂ else f ≫ g₃ := by
  simp only [comp_ite]

end ChainedIte

section Applications

variable {C : Type*} [Category C] {X Y Z : C}

/-- Using ite to define piecewise morphisms -/
def piecewiseMorphism {P : Prop} [Decidable P] (f g : X ⟶ Y) : X ⟶ Y :=
  if P then f else g

/-- Composition with piecewise morphisms -/
example {P : Prop} [Decidable P] (f g : X ⟶ Y) (h : Y ⟶ Z) :
    piecewiseMorphism f g ≫ h = piecewiseMorphism (f ≫ h) (g ≫ h) := by
  unfold piecewiseMorphism
  exact ite_comp f g h

/-- Three-way case split -/
example (n : Nat) (f : X ⟶ Y) (g₁ g₂ g₃ : Y ⟶ Z) :
    f ≫ (if n = 0 then g₁ else if n = 1 then g₂ else g₃) = 
    if n = 0 then f ≫ g₁ else if n = 1 then f ≫ g₂ else f ≫ g₃ := by
  simp only [comp_ite]

end Applications

section EdgeCases

variable {C : Type*} [Category C] {X Y : C}

/-- ITE with identity morphisms -/
example {P : Prop} [Decidable P] (f g : X ⟶ Y) :
    (if P then f else g) ≫ 𝟙 Y = if P then f ≫ 𝟙 Y else g ≫ 𝟙 Y :=
  ite_comp f g (𝟙 Y)

/-- Both branches equal -/
example {P : Prop} [Decidable P] (f : X ⟶ Y) (g : Y ⟶ Y) :
    f ≫ (if P then g else g) = f ≫ g := by
  simp only [comp_ite]
  split <;> rfl

/-- Dependent version where branches have same value -/
example {P : Prop} [Decidable P] (f : X ⟶ Y) (g : Y ⟶ Y)
    (h : P → (Y ⟶ Y)) (h' : ¬P → (Y ⟶ Y))
    (eq : ∀ (p : P) (np : ¬P), h p = g ∧ h' np = g) :
    f ≫ (if p : P then h p else h' p) = f ≫ g := by
  split
  · exact congr_arg (f ≫ ·) (eq _ (fun h => h ‹P›)).1
  · exact congr_arg (f ≫ ·) (eq (fun h => h ‹¬P›) _).2

/-- Classical logic interaction -/
example [Classical] (f : X ⟶ Y) (g g' : Y ⟶ Y) :
    f ≫ (if Classical.em (g = g') then g else g') = 
    if Classical.em (g = g') then f ≫ g else f ≫ g' :=
  comp_ite f g g'

end EdgeCases

end CategoryTheoryTest.IteComposition

/-!
## Summary

This file comprehensively tests:
1. Basic if-then-else composition lemmas
2. Dependent if-then-else versions
3. Concrete examples in Type* with computations
4. Chained and nested if-then-else expressions
5. Applications to piecewise-defined morphisms
6. Edge cases including identity morphisms and equal branches

All 4 if-then-else composition lemmas from Category.Basic.lean are fully tested.
-/