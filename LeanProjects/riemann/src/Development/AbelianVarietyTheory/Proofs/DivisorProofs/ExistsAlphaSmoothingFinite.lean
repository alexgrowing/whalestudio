import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartLeftInvariantLaplacianOpPowEqIterate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySolutiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinitStatement

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
open GlobalTheory.HCAlpha
open scoped ContDiff

namespace GlobalTheory.HCFiniteSm

theorem chart_sum' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (s : Finset ℕ) (c : ℕ → ℂ)
    (ψ : ℕ → Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    chart (∑ k ∈ s, c k • ψ k).1 g y = ∑ k ∈ s, c k * chart (ψ k).1 g y := by
  have hy' : IsUnit (Matrix.of y) := hy
  simp only [chart, dif_pos hy', Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.HCFiniteSm

end
