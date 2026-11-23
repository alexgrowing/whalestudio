import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAt

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_corrDens_eq_zero : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), ∀ {ι : Type} [Fintype ι] (ρ : ι → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) → (∀ y, ∑ i, ρ i y = 1) → ∀ (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ), y ∈ c.e.source → ∑ i, corrDens E H₀ H (ρ i) c y = 0 := by
  intro F _ σ X m E O H H₀ ι _ ρ hρ h1 c y hy
  have hc : IsHoloChart c.e := c.holo
  have key := GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero (fun i v => ρ i (c.e.symm v))
    (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)
    (fun i => (contDiffAt_holoChart hc hy (hρ i y)).differentiableAt (by simp))
    (fun x => h1 _)
  simp only [corrDens, corrTop]
  rw [← Finset.mul_sum, ← Complex.re_sum, key]
  simp

end GlobalTheory.GoodTop
