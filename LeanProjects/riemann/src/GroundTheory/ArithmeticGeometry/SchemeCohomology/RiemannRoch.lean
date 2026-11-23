import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveAdelic
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveCanonical
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveFunctionField
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveProper
import GroundTheory.FunctionField.WeilDifferential

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Module MonoidalCategory

universe w' u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

noncomputable def HLinearEquivOfIso [IsIntegral X] {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    Sheaf.H.{w'} (modulesAb F) n ≃ₗ[k] Sheaf.H.{w'} (modulesAb G) n :=
  ((H.moduleFunctor.{w'} k n).mapIso e).toLinearEquiv

variable [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [IsNormalScheme X]

section Instances

variable (hX : topologicalKrullDim X = 1)

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
include hX in

theorem curve_instances :
    IsNoetherian X ∧ IsLocallyFactorial X ∧ IsFunctionField k X.functionField := by
  have : IsNoetherian X := isNoetherian_of_finiteType (k := k) X
  exact ⟨this, isLocallyFactorial_of_dim_le_one hX.le, isFunctionField X hX⟩

end Instances

section Genus

variable (X) in

noncomputable def structureSheafModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

variable (k X) in

noncomputable def genus : ℕ :=
  finrank k (Sheaf.H.{w'} (modulesAb (structureSheafModule X)) 1)

end Genus

section Degree

noncomputable def sheafDegree (hX : topologicalKrullDim X = 1) {L : X.Modules}
    (hL : IsInvertibleSheaf L) : ℤ :=
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  invertibleDegree (k := k) hL

end Degree

section Canonical

noncomputable def omega (hX : topologicalKrullDim X = 1) : X.Modules :=
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  haveI := (curve_instances (k := k) hX).2.2
  canonicalSheaf (k := k) hX.le

noncomputable def serreDuality (hX : topologicalKrullDim X = 1) {L : X.Modules}
    (hL : IsInvertibleSheaf L) :
    Module.Dual k (Sheaf.H.{w'} (modulesAb L) 1) ≃ₗ[k]
      Sheaf.H.{w'} (modulesAb (omega (k := k) hX ⊗ dualSheaf L)) 0 := by
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  haveI := (curve_instances (k := k) hX).2.2
  let D := divisorOfInvertible hL
  let e : L ≅ divisorSheaf D := asIso (toDivisorSheaf hL)
  let KX := canonicalDivisor (k := k) hX.le
  have hω := canonicalDifferential_ne_zero (k := k) (X := X)
  have hsub : divisorEquiv (k := k) hX.le (KX - D) =
      (canonicalDifferential (k := k) (X := X)).divisor - divisorEquiv (k := k) hX.le D := by
    rw [map_sub, divisorEquiv_canonicalDivisor]
  let t : divisorSheaf KX ⊗ dualSheaf L ≅ divisorSheaf (KX - D) :=
    (nonempty_tensor_dualSheaf_iso KX hL e).some
  exact (((HLinearEquivOfIso e 1).trans (divisorH1EquivAdelic hX.le D)).symm.dualMap.trans
    (WeilDifferential.dualityEquiv hω (divisorEquiv (k := k) hX.le D)).symm).trans
    ((LinearEquiv.ofEq _ _ (congrArg Divisor.L hsub.symm)).trans
      ((divisorH0EquivL hX.le (KX - D)).symm.trans (HLinearEquivOfIso t.symm 0)))

end Canonical

section RiemannRoch

end RiemannRoch

end GroundTheory.Arith.SchemeCoh
