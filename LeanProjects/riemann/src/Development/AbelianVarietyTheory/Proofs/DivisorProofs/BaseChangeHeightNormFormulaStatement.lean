import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeHeightNormFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_height_norm_formula : ∀ (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K''] (m g : ℕ) (h : HermFam K (Fin m → K)) (h'' : HermFam K'' (Fin m → K'')) (σ : K'' →+* ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin m → Fin g → ℂ) (x : Fin m → K''), GlobalTheory.LieHt.IsBC h h'' → (∀ i j, h.form (σ.comp (algebraMap K K'')) (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i)) → h''.nrm σ x = √(Real.pi * (hermForm Hm (∑ k, σ (x k) • W k) (∑ k, σ (x k) • W k)).re) := by
  first | exact @GlobalTheory.LieHt.nrm_eq_sqrt_pi_hermForm | exact GlobalTheory.LieHt.nrm_eq_sqrt_pi_hermForm | (intros; apply GlobalTheory.LieHt.nrm_eq_sqrt_pi_hermForm <;> assumption)
