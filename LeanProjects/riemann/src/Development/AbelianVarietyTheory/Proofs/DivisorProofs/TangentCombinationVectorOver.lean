import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.SecJet

theorem eq_tanComb_of_isLieComb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m : ℕ} {c : Fin m → R}
    {v : Fin m → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) : w = tanComb c v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold tanComb
  congr 2
  funext i
  exact Over.OverMorphism.ext (hu i)

theorem isVecOver_isDiff_tanComb : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (Q : Out.PolAV (Sp ℂ)) (σ : R →+* ℂ) (ψσ : Q.A.left ⟶ P.A.left) (m : ℕ) (v : Fin m → (epsR R ⟶ P.A)) (v₁ : Fin m → (epsR ℂ ⟶ Q.A)) (x : Fin m → R) (g : ℕ) (u : HolUnif Q.A Q.L g) (W : Fin m → Fin g → ℂ), GlobalTheory.IsPolFibre σ P Q ψσ → (∀ k, IsTangent (v k)) → (∀ k, GlobalTheory.IsVecOver σ ψσ (v k) (v₁ k)) → (∀ k, u.IsDiff (W k) (v₁ k)) → GlobalTheory.IsVecOver σ ψσ (GlobalTheory.SecJet.tanComb x v) (GlobalTheory.SecJet.tanComb (fun k => σ (x k)) v₁) ∧ u.IsDiff (∑ k, σ (x k) • W k) (GlobalTheory.SecJet.tanComb (fun k => σ (x k)) v₁) := by
  intro R _ P Q σ ψσ m v v₁ x g u W hψ hv hv₁ hW
  refine ⟨?_, GlobalTheory.isDiff_sum_smul_of_isLieComb Q.A Q.isAb Q.L g m u v₁ W _ _
    (fun k => (hv₁ k).isTangent hψ.2.1 (hv k)) hW (isLieComb_tanComb _ _)⟩
  obtain ⟨w, hw, -⟩ := existsUnique_isVecOver hψ.2.1.1 (tanComb x v)
  have h := Chart.comb_baseChange σ hψ.2.1 (isLieComb_tanComb x v) hv₁ hw
  rw [← eq_tanComb_of_isLieComb h]
  exact hw

end GlobalTheory.SecJet
