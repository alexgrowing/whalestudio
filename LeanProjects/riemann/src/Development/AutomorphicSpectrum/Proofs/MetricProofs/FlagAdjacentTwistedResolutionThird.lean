import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticSpaceNonempty
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietyFirstStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty

theorem anLogRes_W_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)), Nonempty RW.X := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hab hj hk hca hcb RW
  obtain ⟨x⟩ := flagAn_S_nonempty K ι Φ y Ψ N j M n d BM FA
  obtain ⟨l, hl⟩ := BM.O_cover (FA.pr x)
  have hz := GlobalTheory.T.flag_adjacent_arith_variety_first K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hab hj hk hca hcb FA.Re.arith l (FA.pr x) hl
    (fun _ => 1) 0 (fun _ => ⟨?_, by simp⟩)
  · obtain ⟨w, -⟩ := RW.surj _ hz (GlobalTheory.CompanionTheory.Ar.PB.Proj.not_mem_mcPts_top _)
    exact ⟨w⟩
  · intro r s hrs
    exact Matrix.one_apply_ne (fun e => hrs (by simp [e]))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty
