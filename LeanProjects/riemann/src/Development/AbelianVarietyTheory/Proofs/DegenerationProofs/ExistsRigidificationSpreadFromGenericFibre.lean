import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem exists_rigidified : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Rigidified A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Rigidified G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ _ _ hL _ _ _
  obtain ⟨i, hi⟩ := exists_chart hL (eSec G (genericPoint (Sp R)))
  obtain ⟨a, ha, H⟩ := exists_forall_mem (R := R) (V := eSec G ⁻¹ᵁ L.U i) hi
  refine ⟨a, ha, fun R' _ g hg G' _ _ π L' h hL' ⟨w, hw⟩ => ?_⟩
  obtain ⟨t, ht⟩ := AbSquare.exists_gen_of_mem_chart hL (K := PUnit) (fun _ => eSec G' ≫ π) (fun _ => 1)
    (fun _ => i) (fun _ y => (congrArg (fun q => q y ∈ L.U i) (PolBaseChange.eSec_comm h)).mpr (H R' g hg y))
  exact exists_down ((isGen_iff w).1 hw) hL hL' t ht

end GlobalTheory.GenSpread
