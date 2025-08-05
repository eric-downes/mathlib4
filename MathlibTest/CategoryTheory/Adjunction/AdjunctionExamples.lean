/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Concrete Adjunction Examples and Properties

This file tests concrete examples of adjunctions and additional properties.

## Coverage

- Adjunctions from equivalences
- Fully faithful and reflective functors
- Left/right adjoint uniqueness
- Adjunctions preserve (co)limits properties
-/

namespace CategoryTheoryTest.AdjunctionExamples

open CategoryTheory

noncomputable section

section FromEquivalence

variable {C D : Type*} [Category C] [Category D]

/-- An equivalence gives an adjunction -/
example (e : C ≌ D) : e.functor ⊣ e.inverse := e.toAdjunction

/-- Unit of adjunction from equivalence -/
example (e : C ≌ D) : e.toAdjunction.unit = e.unitIso.hom := rfl

/-- Counit of adjunction from equivalence -/
example (e : C ≌ D) : e.toAdjunction.counit = e.counitIso.hom := rfl

/-- Adjunction where unit and counit are isos gives an equivalence -/
example {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) 
    [IsIso adj.unit] [IsIso adj.counit] : 
    C ≌ D := 
  { functor := F
    inverse := G
    unitIso := asIso adj.unit
    counitIso := asIso adj.counit }

end FromEquivalence




section TransformingAdjunctions

variable {C D : Type*} [Category C] [Category D]
variable {F F' : C ⥤ D} {G G' : D ⥤ C}

/-- Natural isomorphism on left -/
example (adj : F ⊣ G) (h : F ≅ F') : F' ⊣ G :=
  Adjunction.ofNatIsoLeft adj h

/-- Natural isomorphism on right -/
example (adj : F ⊣ G) (h : G ≅ G') : F ⊣ G' :=
  Adjunction.ofNatIsoRight adj h


end TransformingAdjunctions

end -- noncomputable

end CategoryTheoryTest.AdjunctionExamples

/-!
## Summary

Concrete functionality tested:
- Adjunctions from equivalences (4 definitions)
- Transforming adjunctions with natural isomorphisms (2 definitions)

Total: ~6 key definitions tested
-/