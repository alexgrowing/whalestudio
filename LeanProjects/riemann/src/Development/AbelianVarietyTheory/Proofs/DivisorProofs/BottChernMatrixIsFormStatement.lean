import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernMatrixIsForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bott_chern_matrix_is_form : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (S : ShortComplex X.Modules) (r s : ℕ) (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s), h.IsCInf → IsForm fun (c : AlgChart p σ D) y => bcMat h hS h₁ h₃ c y := by
  first | exact @GlobalTheory.MixDens.BcMatForm.isForm_bcMat | exact GlobalTheory.MixDens.BcMatForm.isForm_bcMat | (intros; apply GlobalTheory.MixDens.BcMatForm.isForm_bcMat <;> assumption)
