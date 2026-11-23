import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueNeZeroOfRegularUnit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe

theorem upsVal_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X), b ∈ BM.O l → M.blk p = none → upsVal BM l p b ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM l p b hb hp
  obtain ⟨hne, hreg, hreg'⟩ := (BM.good l b hb).2.2 p hp
  exact ValNe.valAt_ne_zero_of_regAt_inv _ _ M.Ω M.x _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) hne hreg hreg'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe
