/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Types
import MathlibTest.CategoryTheory.TestFramework
import MathlibTest.CategoryTheory.Functor.FunctorBasic

/-!
# Tests for Natural Transformations

This file tests the `NatTrans` structure and its basic properties.

## Coverage

- `NatTrans` structure (app, naturality) - ✓ Tested
- `NatTrans.id` - ✓ Tested (identity natural transformation)
- `id_app'` - ✓ Tested
- `vcomp` - ✓ Tested (vertical composition)
- `vcomp_app` - ✓ Tested
- `congr_app` - ✓ Tested

Coverage: 6/6 definitions (100%)
-/

namespace CategoryTheoryTest.NatTransBasic

open CategoryTheory
open CategoryTheoryTest.FunctorBasic -- for doubleFunctor, listFunctor, optionFunctor

section BasicStructure

/-- A natural transformation from doubleFunctor to itself that swaps components -/
def swapNatTrans : NatTrans doubleFunctor doubleFunctor where
  app X := fun (a, b) => (b, a)
  naturality := by
    intros X Y f
    ext ⟨x, y⟩
    simp [doubleFunctor]

/-- Test that naturality holds -/
example {X Y : Type u} (f : X → Y) :
    doubleFunctor.map f ≫ swapNatTrans.app Y = swapNatTrans.app X ≫ doubleFunctor.map f := 
  swapNatTrans.naturality f

/-- Concrete example with natural numbers -/
example : swapNatTrans.app Nat (2, 3) = (3, 2) := rfl

end BasicStructure

section IdentityNatTrans

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

/-- The identity natural transformation really is the identity -/
example (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := 
  NatTrans.id_app' F X

/-- Identity is natural -/
example {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ (NatTrans.id F).app Y = (NatTrans.id F).app X ≫ F.map f := 
  (NatTrans.id F).naturality f

/-- Concrete example with list functor -/
example : (NatTrans.id listFunctor).app Nat [1, 2, 3] = [1, 2, 3] := rfl

/-- Natural transformations are inhabited -/
example : Inhabited (NatTrans F F) := inferInstance

end IdentityNatTrans

section VerticalComposition

variable {C D : Type*} [Category C] [Category D]
variable {F G H : C ⥤ D}

/-- Basic vertical composition -/
example (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (NatTrans.vcomp α β).app X = α.app X ≫ β.app X :=
  NatTrans.vcomp_app α β X

/-- Vertical composition is natural -/
example (α : NatTrans F G) (β : NatTrans G H) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ (NatTrans.vcomp α β).app Y = (NatTrans.vcomp α β).app X ≫ H.map f :=
  (NatTrans.vcomp α β).naturality f

/-- Identity is left unit for vertical composition -/
example (α : NatTrans F G) (X : C) :
    (NatTrans.vcomp (NatTrans.id F) α).app X = α.app X := by
  simp [NatTrans.id_app']

/-- Identity is right unit for vertical composition -/
example (α : NatTrans F G) (X : C) :
    (NatTrans.vcomp α (NatTrans.id G)).app X = α.app X := by
  simp [NatTrans.id_app']

end VerticalComposition

section ConcreteExamples

/-- Natural transformation from list to option that takes the head -/
def headNatTrans : NatTrans listFunctor optionFunctor where
  app _ := List.head?
  naturality := by
    intros X Y f
    ext xs
    cases xs <;> simp [listFunctor, optionFunctor]

example : headNatTrans.app Nat [1, 2, 3] = some 1 := rfl
example : headNatTrans.app Nat [] = none := rfl

/-- Natural transformation from identity to doubleFunctor -/
def diagonalNatTrans : NatTrans (𝟭 (Type u)) doubleFunctor where
  app X := fun x => (x, x)
  naturality := by intros; ext; simp [doubleFunctor]

example : diagonalNatTrans.app Nat (5 : Nat) = (5, 5) := rfl

/-- Composition of natural transformations -/
def composedNatTrans : NatTrans (𝟭 (Type u)) doubleFunctor :=
  NatTrans.vcomp diagonalNatTrans swapNatTrans

example : composedNatTrans.app Nat (7 : Nat) = (7, 7) := rfl

end ConcreteExamples

section CongrApp

variable {C D : Type*} [Category C] [Category D]
variable {F G : C ⥤ D}

/-- Test congr_app -/
example {α β : NatTrans F G} (h : α = β) (X : C) : 
    α.app X = β.app X :=
  congr_app h X

/-- Concrete example showing congr_app -/
example (h : (swapNatTrans : NatTrans (doubleFunctor : Type 0 ⥤ Type 0) doubleFunctor) = swapNatTrans) :
    swapNatTrans.app Nat = swapNatTrans.app Nat :=
  congr_app h Nat

end CongrApp

section NaturalityDiagram

variable {C D : Type*} [Category C] [Category D]

/-- The naturality square commutes for any natural transformation -/
example {F G : C ⥤ D} (α : NatTrans F G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ α.app Y = α.app X ≫ G.map f := by
  simp -- Uses the simp lemma NatTrans.naturality

/-- Extended naturality diagram from the example in NatTrans.lean -/
example {F G : C ⥤ D} (α : NatTrans F G) {X Y U V : C} 
    (f : X ⟶ Y) (g : Y ⟶ U) (h : U ⟶ V) :
    α.app X ≫ G.map f ≫ G.map g ≫ G.map h = F.map f ≫ F.map g ≫ F.map h ≫ α.app V := by
  simp

end NaturalityDiagram

section EdgeCases

/-- Natural transformation between constant functors -/
def constNatTrans {C D : Type*} [Category C] [Category D] (X Y : D) (f : X ⟶ Y) :
    NatTrans (@constFunctor C D _ _ X) (constFunctor Y) where
  app _ := f
  naturality := by intros; simp [constFunctor]

/-- Vertical composition is associative -/
example {C D : Type*} [Category C] [Category D] 
    {F G H I : C ⥤ D} (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H I) (X : C) :
    (NatTrans.vcomp (NatTrans.vcomp α β) γ).app X = 
    (NatTrans.vcomp α (NatTrans.vcomp β γ)).app X := by
  simp

end EdgeCases

end CategoryTheoryTest.NatTransBasic

/-!
## Summary

This file comprehensively tests:
1. Basic natural transformation structure with app and naturality
2. Identity natural transformation and its properties
3. Vertical composition of natural transformations
4. Concrete examples (swap, head, diagonal)
5. Congruence for components
6. Naturality diagrams and extended naturality
7. Edge cases including constant functors and associativity

All 6 public definitions from NatTrans.lean are fully tested.
-/