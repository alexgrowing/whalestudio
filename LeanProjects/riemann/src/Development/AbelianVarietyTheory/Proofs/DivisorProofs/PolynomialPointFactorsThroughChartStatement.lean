import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialPointFactorsThroughChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_point_factors_through_chart : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (U : B.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (N : Type) (n : N → Γ(Y, W)) (ψ : Spec (CommRingCat.of (MvPolynomial N Γ(B, U))) ⟶ Y), ψ ≫ π = Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U))) ≫ hU.fromSpec → ∀ (hψ : ⊤ ≤ ψ ⁻¹ᵁ W), (∀ s, (ψ.appLE W ⊤ hψ).hom (n s) = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).inv.hom (MvPolynomial.X s)) → W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n)) ≫ ψ = W.ι → IsAffineOpen W ∧ Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) := by
  first | exact @GlobalTheory.FlagCell.isAffineOpen_and_bijective_of_section | exact GlobalTheory.FlagCell.isAffineOpen_and_bijective_of_section | (intros; apply GlobalTheory.FlagCell.isAffineOpen_and_bijective_of_section <;> assumption)
