/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
# Core Tests for Equalizers and Coequalizers

This file tests essential APIs for equalizers and coequalizers.

## Coverage

- Equalizer and coequalizer constructions
- Fork and cofork structures
- Universal properties
- Basic examples in Type*
-/

namespace CategoryTheoryTest.EqualizersCore

open CategoryTheory CategoryTheory.Limits

noncomputable section

section BasicEqualizers

variable {C : Type*} [Category C]

/-- Walking parallel pair as index -/
example : WalkingParallelPair.zero ≠ WalkingParallelPair.one := by simp

/-- Equalizer exists -/
example {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g] : C := equalizer f g

/-- Equalizer inclusion -/
example {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g] : equalizer f g ⟶ X := equalizer.ι f g

/-- Equalizer property -/
example {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g] : 
    equalizer.ι f g ≫ f = equalizer.ι f g ≫ g := equalizer.condition f g

/-- Equalizer lift -/
example {X Y Z : C} (f g : X ⟶ Y) [HasEqualizer f g] (h : Z ⟶ X) (w : h ≫ f = h ≫ g) :
    Z ⟶ equalizer f g := equalizer.lift h w

/-- Lift equation -/
example {X Y Z : C} (f g : X ⟶ Y) [HasEqualizer f g] (h : Z ⟶ X) (w : h ≫ f = h ≫ g) :
    equalizer.lift h w ≫ equalizer.ι f g = h := by simp


end BasicEqualizers

section BasicCoequalizers

variable {C : Type*} [Category C]

/-- Coequalizer exists -/
example {X Y : C} (f g : X ⟶ Y) [HasCoequalizer f g] : C := coequalizer f g

/-- Coequalizer projection -/
example {X Y : C} (f g : X ⟶ Y) [HasCoequalizer f g] : Y ⟶ coequalizer f g := coequalizer.π f g

/-- Coequalizer property -/
example {X Y : C} (f g : X ⟶ Y) [HasCoequalizer f g] : 
    f ≫ coequalizer.π f g = g ≫ coequalizer.π f g := coequalizer.condition f g

/-- Coequalizer desc -/
example {X Y Z : C} (f g : X ⟶ Y) [HasCoequalizer f g] (h : Y ⟶ Z) (w : f ≫ h = g ≫ h) :
    coequalizer f g ⟶ Z := coequalizer.desc h w

/-- Desc equation -/
example {X Y Z : C} (f g : X ⟶ Y) [HasCoequalizer f g] (h : Y ⟶ Z) (w : f ≫ h = g ≫ h) :
    coequalizer.π f g ≫ coequalizer.desc h w = h := by simp

end BasicCoequalizers

section Forks

variable {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y)

/-- Fork construction -/
example (E : C) (e : E ⟶ X) (w : e ≫ f = e ≫ g) : Fork f g :=
  Fork.ofι e w

/-- Fork tip -/
example (s : Fork f g) : C := s.pt

/-- Fork inclusion -/
example (s : Fork f g) : s.pt ⟶ X := s.ι

/-- Fork condition -/
example (s : Fork f g) : s.ι ≫ f = s.ι ≫ g := s.condition

/-- Cofork construction -/
example (E : C) (e : Y ⟶ E) (w : f ≫ e = g ≫ e) : Cofork f g :=
  Cofork.ofπ e w

/-- Cofork tip -/
example (s : Cofork f g) : C := s.pt

/-- Cofork projection -/
example (s : Cofork f g) : Y ⟶ s.pt := s.π

/-- Cofork condition -/
example (s : Cofork f g) : f ≫ s.π = g ≫ s.π := s.condition

end Forks

section TypeExamples

/-- Type has equalizers -/
instance : HasEqualizers.{u} (Type u) := inferInstance

/-- Type has coequalizers -/
instance : HasCoequalizers.{u} (Type u) := inferInstance


end TypeExamples

section Typeclasses

/-- HasEqualizers instance -/
example : HasEqualizers (Type u) := inferInstance

/-- HasCoequalizers instance -/
example : HasCoequalizers (Type u) := inferInstance


end Typeclasses

end -- noncomputable

end CategoryTheoryTest.EqualizersCore

/-!
## Summary

Core functionality tested:
- Equalizer/coequalizer construction (~6 definitions)
- Fork/cofork structures (~8 definitions)
- Universal properties (~4 definitions)
- Type examples (~4 definitions)
- Typeclass instances (~4 definitions)

Total: ~18 key definitions tested
-/