import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIdealNormSuccessiveMinimum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_ideal_norm_successive_minimum : ∀ {K : Type} [Field K] [NumberField K] {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {n r : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (v : Fin r → Fin n → K) (i : Fin r), Full L → LinearIndependent K v → 0 < (⨆ a : grIdeal L v i, ‖j a‖) ∧ sInf {ρ : ℝ | ∃ d : Fin r → C, d i ≠ 0 ∧ (∀ k, i < k → d k = 0) ∧ (∑ k, d k • fun m => j (v k m)) ∈ latC j L ∧ ρ = ‖d i‖⁻¹} = (⨆ a : grIdeal L v i, ‖j a‖)⁻¹ := by
  first | exact @GlobalTheory.LieSmooth.grNorm_latC_eq_inv_iSup | exact GlobalTheory.LieSmooth.grNorm_latC_eq_inv_iSup | (intros; apply GlobalTheory.LieSmooth.grNorm_latC_eq_inv_iSup <;> assumption)
