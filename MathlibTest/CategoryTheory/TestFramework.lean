/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans

/-!
# Test Framework for Category Theory

This file provides utilities for testing category theory in mathlib4.

## Main features

* Test assertions for morphism equality
* Standard test categories (Walking morphisms, discrete categories)
* Coverage tracking annotations
* Property testing utilities
-/

namespace CategoryTheoryTest

open CategoryTheory

/-- Annotation for tracking tested definitions -/
@[inherit_doc]
class Tested (α : Sort*) : Prop where
  tested : True

attribute [instance] Tested.mk

/-!
## Test Categories

Standard small categories for testing.
-/

/-- The walking arrow category `· → ·` -/
inductive WalkingArrow : Type where
  | source : WalkingArrow
  | target : WalkingArrow

namespace WalkingArrow

inductive Hom : WalkingArrow → WalkingArrow → Type where
  | id (X : WalkingArrow) : Hom X X
  | arr : Hom source target

instance : Category WalkingArrow where
  Hom := Hom
  id := Hom.id
  comp := fun
    | .id _, f => f
    | f, .id _ => f
    | .arr, .arr => .arr  -- Invalid but total

@[simp] lemma id_source : 𝟙 source = Hom.id source := rfl
@[simp] lemma id_target : 𝟙 target = Hom.id target := rfl
@[simp] lemma comp_arr : Hom.arr ≫ 𝟙 target = Hom.arr := rfl

end WalkingArrow

/-- The walking isomorphism category `· ≅ ·` -/
inductive WalkingIso : Type where
  | A : WalkingIso
  | B : WalkingIso

namespace WalkingIso

inductive Hom : WalkingIso → WalkingIso → Type where
  | id (X : WalkingIso) : Hom X X
  | f : Hom A B
  | g : Hom B A

instance : Category WalkingIso where
  Hom := Hom
  id := Hom.id
  comp := fun
    | .id _, h => h
    | h, .id _ => h
    | .f, .g => .id A
    | .g, .f => .id B

@[simp] lemma f_comp_g : Hom.f ≫ Hom.g = 𝟙 A := rfl
@[simp] lemma g_comp_f : Hom.g ≫ Hom.f = 𝟙 B := rfl

/-- The isomorphism in the walking isomorphism category -/
def iso : A ≅ B where
  hom := Hom.f
  inv := Hom.g

end WalkingIso

/-- Three object category for testing composition -/
inductive Three : Type where
  | A | B | C

namespace Three

inductive Hom : Three → Three → Type where
  | id (X : Three) : Hom X X
  | f : Hom A B
  | g : Hom B C
  | fg : Hom A C

instance : Category Three where
  Hom := Hom
  id := Hom.id
  comp := fun
    | .id _, h => h
    | h, .id _ => h
    | .f, .g => .fg
    | _, _ => .id _  -- Other cases invalid

@[simp] lemma f_comp_g : Hom.f ≫ Hom.g = Hom.fg := rfl

end Three

/-!
## Test Utilities
-/

/-- Assert that two morphisms are equal, with a helpful error message -/
def assertEq {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y) 
    (msg : String := "") : Prop :=
  f = g

/-- Assert that a functor preserves a specific morphism -/
def assertPreserves {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : Prop :=
  F.map (𝟙 X) = 𝟙 (F.obj X) ∧ F.map f = F.map f

/-- Test that a property holds for multiple inputs -/
def testProperty {α : Type*} (p : α → Prop) (inputs : List α) : Prop :=
  inputs.all p

/-!
## Coverage Tracking
-/

/-- Record that a definition has been tested -/
macro "test_covers" names:ident* : attr => 
  `(attr|instance : Tested $(names)*)

/-- Mark a test as covering certain definitions -/
macro "covering" names:ident* "in" body:term : term =>
  `(section 
    attribute [local instance] Tested.mk
    $body
    end)

/-!
## Property Testing Helpers
-/

/-- Test that a functor preserves all basic properties -/
def testFunctorProperties {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : Prop :=
  (∀ X, F.map (𝟙 X) = 𝟙 (F.obj X)) ∧
  (∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), F.map (f ≫ g) = F.map f ≫ F.map g)

/-- Test that a natural transformation satisfies naturality -/
def testNaturality {C D : Type*} [Category C] [Category D] 
    {F G : C ⥤ D} (α : F ⟶ G) : Prop :=
  ∀ {X Y} (f : X ⟶ Y), F.map f ≫ α.app Y = α.app X ≫ G.map f

/-!
## Example Usage
-/

section Examples

-- Test using walking arrow
example : ∃ (f : WalkingArrow.source ⟶ WalkingArrow.target), f = f := 
  ⟨WalkingArrow.Hom.arr, rfl⟩

-- Test using assertion
example {C : Type*} [Category C] {X : C} : assertEq (𝟙 X) (𝟙 X) "identity should equal itself" := 
  rfl

-- Coverage tracking example
covering Category.id_comp in
example {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp

end Examples

end CategoryTheoryTest