import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemExistsRootOfUnitySumNormAttained
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_exists_rootOfUnity_sum_norm_attained : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (B : ℝ), (∀ (t : T) i, ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ ≤ B) → (∃ (t : T) (i : S.J), B ≤ ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖) → ∃ (k : _) (hk : S.FF T c k ∈ S.R), ‖y₀ ⟨S.FF T c k, hk⟩‖ = B := by
  first | exact @GlobalTheory.thetaSys_exists_norm_FF_eq | exact GlobalTheory.thetaSys_exists_norm_FF_eq | (intros; apply GlobalTheory.thetaSys_exists_norm_FF_eq <;> assumption)
