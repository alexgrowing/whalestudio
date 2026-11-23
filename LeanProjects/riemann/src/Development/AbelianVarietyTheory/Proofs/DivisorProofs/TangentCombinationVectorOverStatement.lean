import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationVectorOver
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
theorem _root_.GlobalTheory.T.tangent_combination_vector_over : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (Q : Out.PolAV (Sp ℂ)) (σ : R →+* ℂ) (ψσ : Q.A.left ⟶ P.A.left) (m : ℕ) (v : Fin m → (epsR R ⟶ P.A)) (v₁ : Fin m → (epsR ℂ ⟶ Q.A)) (x : Fin m → R) (g : ℕ) (u : HolUnif Q.A Q.L g) (W : Fin m → Fin g → ℂ), GlobalTheory.IsPolFibre σ P Q ψσ → (∀ k, IsTangent (v k)) → (∀ k, GlobalTheory.IsVecOver σ ψσ (v k) (v₁ k)) → (∀ k, u.IsDiff (W k) (v₁ k)) → GlobalTheory.IsVecOver σ ψσ (GlobalTheory.SecJet.tanComb x v) (GlobalTheory.SecJet.tanComb (fun k => σ (x k)) v₁) ∧ u.IsDiff (∑ k, σ (x k) • W k) (GlobalTheory.SecJet.tanComb (fun k => σ (x k)) v₁) := by
  first | exact @GlobalTheory.SecJet.isVecOver_isDiff_tanComb | exact GlobalTheory.SecJet.isVecOver_isDiff_tanComb | (intros; apply GlobalTheory.SecJet.isVecOver_isDiff_tanComb <;> assumption)
