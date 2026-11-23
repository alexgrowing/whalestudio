import Mathlib
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

section Tower

variable (K E F : Type u) [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [Normal K E]

noncomputable def unitsTowerHom :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E) (galUnits.{u} K E) ⟶
      galUnits.{u} K F :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Eˣ) (B := Additive Fˣ) (MonoidHom.toAdditive
    (Units.map ((algebraMap E F : E →+* F) : E →* F))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ E ((Additive.toMul (α := Eˣ) x : Eˣ) : E)⟩

@[simp]
theorem unitsTowerHom_hom_apply (x : Additive Eˣ) :
    ((Additive.toMul (α := Fˣ) ((unitsTowerHom K E F).hom x) : Fˣ) : F) =
      algebraMap E F ((Additive.toMul (α := Eˣ) x : Eˣ) : E) :=
  rfl

noncomputable def unitsInflationTower (n : ℕ) :
    groupCohomology (galUnits.{u} K E) n ⟶ groupCohomology (galUnits.{u} K F) n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom E) (unitsTowerHom K E F) n

end Tower

section LE

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {E F : IntermediateField K L}
  (h : E ≤ F) [Normal K E]

noncomputable def galRestrictOfLE : Gal(F/K) →* Gal(E/K) :=
  letI : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  AlgEquiv.restrictNormalHom E

theorem coe_galRestrictOfLE_apply (σ : Gal(F/K)) (x : E) :
    ((galRestrictOfLE h σ x : E) : L) = ((σ (IntermediateField.inclusion h x) : F) : L) := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact congrArg (fun y : F => (y : L)) (AlgEquiv.restrictNormal_commutes σ E x)

noncomputable def unitsOfLE :
    Rep.res (galRestrictOfLE h) (galUnits.{u} K E) ⟶ galUnits.{u} K F :=
  letI : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  unitsTowerHom K E F

@[simp]
theorem coe_unitsOfLE_hom_apply (x : Additive Eˣ) :
    (((Additive.toMul (α := Fˣ) ((unitsOfLE h).hom x) : Fˣ) : F) : L) =
      (((Additive.toMul (α := Eˣ) x : Eˣ) : E) : L) :=
  rfl

noncomputable def unitsInflationOfLE (n : ℕ) :
    groupCohomology (galUnits.{u} K E) n ⟶ groupCohomology (galUnits.{u} K F) n :=
  groupCohomology.map (galRestrictOfLE h) (unitsOfLE h) n

end LE

end GroundTheory.ProfCoh
