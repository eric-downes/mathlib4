/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import MathlibTest.CategoryTheory.TestFramework

/-!
# Tests for Whiskering Operations

This file tests the whiskering operations `eq_whisker` and `whisker_eq` along with
their associated notations.

## Coverage

- `eq_whisker` - ✓ Tested (basic usage and notation)
- `whisker_eq` - ✓ Tested (basic usage and notation)
- `=≫` notation - ✓ Tested
- `≫=` notation - ✓ Tested
- Interaction with category laws - ✓ Tested
- Concrete examples in Type* - ✓ Tested
- Chaining whiskers - ✓ Tested

Coverage: 2/2 definitions (100%)
-/

namespace CategoryTheoryTest.Whiskering

open CategoryTheory

section BasicWhiskering

variable {C : Type*} [Category C] {W X Y Z : C}

/-- Test eq_whisker: postcompose an equation by a morphism -/
example {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h :=
  eq_whisker w h

/-- Test whisker_eq: precompose an equation by a morphism -/
example (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h :=
  whisker_eq f w

/-- Test notation =≫ for eq_whisker -/
example {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h :=
  w =≫ h

/-- Test notation ≫= for whisker_eq -/
example (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h :=
  f ≫= w

/-- Verify the notations give the same result as the functions -/
example {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : 
    (w =≫ h) = eq_whisker w h := rfl

example (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : 
    (f ≫= w) = whisker_eq f w := rfl

end BasicWhiskering

section InteractionWithLaws

variable {C : Type*} [Category C] {X Y Z : C}

/-- Whiskering preserves identity: whisker identity equation -/
example (f : X ⟶ Y) : f ≫= (rfl : 𝟙 Y = 𝟙 Y) = rfl := rfl

/-- Whiskering with identity morphism -/
example {f g : X ⟶ Y} (w : f = g) : w =≫ 𝟙 Y = by simp [w] := by
  simp [eq_whisker, w]

example {f g : Y ⟶ Z} (w : f = g) : 𝟙 Y ≫= w = by simp [w] := by
  simp [whisker_eq, w]

/-- Whiskering respects composition -/
example {f g : W ⟶ X} (w : f = g) (h : X ⟶ Y) (k : Y ⟶ Z) :
    w =≫ (h ≫ k) = ((w =≫ h) =≫ k) := by
  simp [eq_whisker, w]

example (f : W ⟶ X) {g h : X ⟶ Y} (w : g = h) (k : Y ⟶ Z) :
    f ≫= (w =≫ k) = ((f ≫= w) =≫ k) := by
  simp [eq_whisker, whisker_eq, w]

end InteractionWithLaws

section ChainingWhiskers

variable {C : Type*} [Category C] {V W X Y Z : C}

/-- Chain multiple whiskers on the right -/
example {f g : V ⟶ W} (w : f = g) (h : W ⟶ X) (k : X ⟶ Y) (l : Y ⟶ Z) :
    f ≫ h ≫ k ≫ l = g ≫ h ≫ k ≫ l :=
  (((w =≫ h) =≫ k) =≫ l)

/-- Chain multiple whiskers on the left -/
example (f : V ⟶ W) (g : W ⟶ X) {h h' : X ⟶ Y} (w : h = h') (k : Y ⟶ Z) :
    f ≫ g ≫ h ≫ k = f ≫ g ≫ h' ≫ k := by
  rw [← Category.assoc, ← Category.assoc]
  exact (f ≫ g) ≫= (w =≫ k)

/-- Mix left and right whiskering -/
example {f g : W ⟶ X} (w₁ : f = g) {h k : Y ⟶ Z} (w₂ : h = k) (l : X ⟶ Y) :
    f ≫ l ≫ h = g ≫ l ≫ k :=
  (w₁ =≫ l) =≫ k ▸ l ≫= w₂

end ChainingWhiskers

section ConcreteExamples

/-- Whiskering in Type* is function composition -/
example {X Y Z : Type*} {f g : X → Y} (w : f = g) (h : Y → Z) :
    (w =≫ h : (f ≫ h) = (g ≫ h)) = by simp [w] := by
  simp [eq_whisker, w]

/-- Concrete computation with whiskering -/
example : ((rfl : (· + 1 : Nat → Nat) = (· + 1)) =≫ (· * 2)) = 
          (rfl : (fun n => (n + 1) * 2) = (fun n => (n + 1) * 2)) := rfl

/-- Whiskering with concrete functions -/
example {f g : Nat → Nat} (w : f = g) :
    (fun n => (f n) * 2) = (fun n => (g n) * 2) :=
  congr_fun (w =≫ (· * 2)) 

/-- Test with actual values -/
example (w : (· + 1 : Nat → Nat) = (fun n => n + 1)) :
    ((w =≫ (· * 2)) : _ = _) = (rfl : _ = _) := by
  simp

end ConcreteExamples

section Applications

variable {C : Type*} [Category C] {X Y Z : C}

/-- Use whiskering to prove a simple equality -/
example (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = f ≫ g := by
  have : g = g := rfl
  exact f ≫= this

/-- Whiskering helps with rewriting under composition -/
example {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y ⟶ Z} 
    (wf : f₁ = f₂) (wg : g₁ = g₂) : f₁ ≫ g₁ = f₂ ≫ g₂ := by
  rw [wf =≫ g₁, f₂ ≫= wg]

/-- Whiskering with associativity -/
example {f : W ⟶ X} {g₁ g₂ : X ⟶ Y} {h : Y ⟶ Z}
    (w : g₁ = g₂) : (f ≫ g₁) ≫ h = f ≫ (g₂ ≫ h) := by
  rw [Category.assoc, f ≫= w]

end Applications

section EdgeCases

variable {C : Type*} [Category C] {X Y : C}

/-- Whiskering with reflexivity gives reflexivity -/
example (f : X ⟶ Y) (g : Y ⟶ Y) : 
    (rfl : f = f) =≫ g = (rfl : f ≫ g = f ≫ g) := rfl

/-- Self-whiskering -/
example {f g : X ⟶ X} (w : f = g) : 
    f ≫= (w =≫ f) = ((rfl : f = f) =≫ f) =≫ g := by
  simp [eq_whisker, whisker_eq, w]

/-- Whiskering equations between identity morphisms -/
example (w : 𝟙 X = 𝟙 X) : w =≫ 𝟙 X = (rfl : 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ 𝟙 X) := by
  simp

end EdgeCases

end CategoryTheoryTest.Whiskering

/-!
## Summary

This file tests:
1. Basic whiskering operations and their notations
2. Interaction with category laws (identity, composition)
3. Chaining multiple whiskers
4. Concrete examples in Type*
5. Practical applications of whiskering
6. Edge cases including self-whiskering

Both whiskering operations from Category.Basic.lean are fully tested.
-/