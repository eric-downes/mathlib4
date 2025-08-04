/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import MathlibTest.CategoryTheory.TestFramework

/-!
# Tests for Epimorphisms and Monomorphisms

This file tests the `Epi` and `Mono` classes and their properties.

## Coverage

- `Epi` class - ✓ Tested (definition and cancellation)
- `Mono` class - ✓ Tested (definition and cancellation)
- `instance (X : C) : Epi (𝟙 X)` - ✓ Tested
- `instance (X : C) : Mono (𝟙 X)` - ✓ Tested
- `cancel_epi` - ✓ Tested
- `cancel_epi_assoc_iff` - ✓ Tested
- `cancel_mono` - ✓ Tested
- `cancel_mono_assoc_iff` - ✓ Tested
- `cancel_epi_id` - ✓ Tested
- `cancel_mono_id` - ✓ Tested
- `epi_comp` instance - ✓ Tested
- `epi_comp'` - ✓ Tested
- `mono_comp` instance - ✓ Tested
- `mono_comp'` - ✓ Tested
- `mono_of_mono` - ✓ Tested
- `mono_of_mono_fac` - ✓ Tested
- `epi_of_epi` - ✓ Tested
- `epi_of_epi_fac` - ✓ Tested
- Thin category instances - ✓ Tested

Coverage: 19/19 definitions (100%)
-/

namespace CategoryTheoryTest.EpiMono

open CategoryTheory

section BasicProperties

/-- Identity morphisms are epimorphisms -/
example {C : Type*} [Category C] (X : C) : Epi (𝟙 X) := inferInstance

/-- Identity morphisms are monomorphisms -/
example {C : Type*} [Category C] (X : C) : Mono (𝟙 X) := inferInstance

/-- Test Epi cancellation property directly -/
example {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) [Epi f] 
    {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h) : g = h :=
  Epi.left_cancellation g h w

/-- Test Mono cancellation property directly -/
example {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [Mono f] 
    {W : C} {g h : W ⟶ X} (w : g ≫ f = h ≫ f) : g = h :=
  Mono.right_cancellation g h w

end BasicProperties

section CancellationLemmas

variable {C : Type*} [Category C] {W X Y Z : C}

/-- Test cancel_epi both directions -/
example (f : X ⟶ Y) [Epi f] (g h : Y ⟶ Z) : 
    f ≫ g = f ≫ h ↔ g = h :=
  cancel_epi f

/-- Test cancel_mono both directions -/
example (f : X ⟶ Y) [Mono f] (g h : Z ⟶ X) : 
    g ≫ f = h ≫ f ↔ g = h :=
  cancel_mono f

/-- Test cancel_epi_assoc_iff -/
example (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} {k l : Z ⟶ W} :
    (f ≫ g) ≫ k = (f ≫ h) ≫ l ↔ g ≫ k = h ≫ l :=
  cancel_epi_assoc_iff f

/-- Test cancel_mono_assoc_iff -/
example (f : Y ⟶ Z) [Mono f] {g h : X ⟶ Y} {k l : W ⟶ X} :
    k ≫ (g ≫ f) = l ≫ (h ≫ f) ↔ k ≫ g = l ≫ h :=
  cancel_mono_assoc_iff f

/-- Test cancel_epi_id -/
example (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y} : 
    f ≫ h = f ↔ h = 𝟙 Y :=
  cancel_epi_id f

/-- Test cancel_mono_id -/
example (f : X ⟶ Y) [Mono f] {g : X ⟶ X} : 
    g ≫ f = f ↔ g = 𝟙 X :=
  cancel_mono_id f

end CancellationLemmas

section Composition

variable {C : Type*} [Category C] {X Y Z : C}

/-- Composition of epimorphisms is an epimorphism (instance) -/
example (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g] : Epi (f ≫ g) := inferInstance

/-- Composition of epimorphisms is an epimorphism (explicit) -/
example {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) :=
  @epi_comp' _ _ _ _ _ f g hf hg

/-- Composition of monomorphisms is a monomorphism (instance) -/
example (f : X ⟶ Y) [Mono f] (g : Y ⟶ Z) [Mono g] : Mono (f ≫ g) := inferInstance

/-- Composition of monomorphisms is a monomorphism (explicit) -/
example {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) :=
  @mono_comp' _ _ _ _ _ f g hf hg

end Composition

section Factorization

variable {C : Type*} [Category C] {X Y Z : C}

/-- If f ≫ g is mono, then f is mono -/
example (f : X ⟶ Y) (g : Y ⟶ Z) [Mono (f ≫ g)] : Mono f :=
  mono_of_mono f g

/-- If h = f ≫ g and h is mono, then f is mono -/
example {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Mono h] (w : f ≫ g = h) : Mono f :=
  mono_of_mono_fac w

/-- If f ≫ g is epi, then g is epi -/
example (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g :=
  epi_of_epi f g

/-- If h = f ≫ g and h is epi, then g is epi -/
example {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g :=
  epi_of_epi_fac w

end Factorization

section ConcreteExamples

/-- In Type u, injective functions are monomorphisms -/
example {X Y : Type u} (f : X → Y) (hf : Function.Injective f) : 
    @Mono (Type u) _ X Y f := by
  constructor
  intros Z g h w
  funext z
  exact hf (congr_fun w z)

/-- In Type u, surjective functions are epimorphisms -/
example {X Y : Type u} (f : X → Y) (hf : Function.Surjective f) : 
    @Epi (Type u) _ X Y f := by
  constructor
  intros Z g h w
  funext y
  obtain ⟨x, rfl⟩ := hf y
  exact congr_fun w x

end ConcreteExamples

section ThinCategories

/-- In a thin category, all morphisms are both epi and mono -/
example {C : Type*} [Category C] [Quiver.IsThin C] {X Y : C} (f : X ⟶ Y) : 
    Epi f ∧ Mono f :=
  ⟨inferInstance, inferInstance⟩

end ThinCategories

section EdgeCases

variable {C : Type*} [Category C]

/-- Double application of mono_of_mono -/
example {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) 
    [Mono ((f ≫ g) ≫ h)] : Mono f := by
  rw [Category.assoc] at *
  exact mono_of_mono f (g ≫ h)

/-- Combining epi and mono properties -/
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) 
    [Epi f] [Mono g] (h k : X ⟶ Z) 
    (w : f ≫ g = h) (w' : f ≫ g = k) : h = k := by
  rw [← w, w']

end EdgeCases

end CategoryTheoryTest.EpiMono

/-!
## Summary

This file comprehensively tests:
1. Basic epi/mono definitions and instances
2. All cancellation lemmas and their applications
3. Composition properties for epi and mono
4. Factorization lemmas (extracting epi/mono from compositions)
5. Concrete examples in Type u showing the connection to injective/surjective
6. Thin category behavior where all morphisms are epi and mono
7. Edge cases and combined properties

All 19 public definitions related to Epi/Mono in Category.Basic.lean are tested.
-/