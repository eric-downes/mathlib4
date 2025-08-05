/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Core Tests for Terminal and Initial Objects

This file tests the essential APIs for terminal and initial objects.

## Coverage

- `IsTerminal` predicate
- `IsInitial` predicate  
- `HasTerminal` typeclass
- `HasInitial` typeclass
- Basic constructions and properties
-/

namespace CategoryTheoryTest.TerminalCore

open CategoryTheory CategoryTheory.Limits

noncomputable section

section BasicPredicates

/-- PUnit is terminal in Type* -/
example : IsTerminal (PUnit : Type*) := Types.isTerminalPunit

/-- PEmpty is initial in Type* -/
example : IsInitial (PEmpty : Type*) := Types.isInitialPunit

/-- Morphisms to terminal are unique -/
example {X : Type*} (f g : X → PUnit) : f = g := by
  ext

/-- Morphisms from initial are unique -/
example {X : Type*} (f g : PEmpty → X) : f = g := by
  ext x
  exact PEmpty.elim x

end BasicPredicates

section PreorderExamples

/-- Top element is terminal in a preorder -/
example {P : Type*} [Preorder P] [OrderTop P] : IsTerminal (⊤ : P) := 
  isTerminalTop

/-- Bottom element is initial in a preorder -/
example {P : Type*} [Preorder P] [OrderBot P] : IsInitial (⊥ : P) := 
  isInitialBot

/-- Example: true is terminal in Bool -/
example : @IsTerminal Bool _ true := by
  apply @isTerminalTop Bool _ _

/-- Example: false is initial in Bool -/
example : @IsInitial Bool _ false := by
  apply @isInitialBot Bool _ _

end PreorderExamples

section Typeclasses

/-- Type* has terminal object -/
example : HasTerminal (Type*) := inferInstance

/-- Type* has initial object -/
example : HasInitial (Type*) := inferInstance

/-- The terminal object is terminal -/
example : IsTerminal (⊤_ (Type*)) := terminalIsTerminal

/-- The initial object is initial -/
example : IsInitial (⊥_ (Type*)) := initialIsInitial

/-- Get morphism to terminal -/
example (X : Type u) : X ⟶ ⊤_ (Type u) := terminal.from X

/-- Get morphism from initial -/
example (X : Type u) : ⊥_ (Type u) ⟶ X := initial.to X

/-- Composition properties -/
example {X Y : Type u} (f : X ⟶ Y) : 
    f ≫ terminal.from Y = terminal.from X := by
  simp

example {X Y : Type u} (f : X ⟶ Y) : 
    initial.to X ≫ f = initial.to Y := by
  simp

end Typeclasses

section GeneralProperties

variable {C : Type*} [Category C]

/-- Terminal objects are unique up to iso -/
example {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : 
    Nonempty (T ≅ T') := ⟨hT.uniqueUpToIso hT'⟩

/-- Initial objects are unique up to iso -/
example {I I' : C} (hI : IsInitial I) (hI' : IsInitial I') : 
    Nonempty (I ≅ I') := ⟨hI.uniqueUpToIso hI'⟩

/-- Morphisms from terminal are mono -/
example {T X : C} (hT : IsTerminal T) (f : T ⟶ X) : Mono f :=
  hT.mono_from f

/-- Morphisms to initial are epi -/
example {I X : C} (hI : IsInitial I) (f : X ⟶ I) : Epi f :=
  hI.epi_to f

/-- Transport along isomorphism -/
example {X Y : C} (hX : IsTerminal X) (e : X ≅ Y) : IsTerminal Y :=
  IsTerminal.ofIso hX e

example {X Y : C} (hX : IsInitial X) (e : X ≅ Y) : IsInitial Y :=
  IsInitial.ofIso hX e

end GeneralProperties

section OppositeCategory

/-- Terminal in C is initial in Cᵒᵖ -/
example {C : Type*} [Category C] [HasTerminal C] : HasInitial Cᵒᵖ := 
  inferInstance

/-- Initial in C is terminal in Cᵒᵖ -/
example {C : Type*} [Category C] [HasInitial C] : HasTerminal Cᵒᵖ := 
  inferInstance

end OppositeCategory

end -- noncomputable

end CategoryTheoryTest.TerminalCore

/-!
## Summary

Core functionality tested:
- IsTerminal/IsInitial predicates (2 definitions)
- HasTerminal/HasInitial typeclasses (2 definitions)
- terminal.from/initial.to morphisms (2 definitions)
- terminalIsTerminal/initialIsInitial (2 definitions)
- Uniqueness properties (2 definitions)
- Mono/epi properties (2 definitions)
- Transport along iso (2 definitions)
- Opposite category (2 definitions)

Total: ~16 core definitions tested
-/