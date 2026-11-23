import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartFlagAnalyticMapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothMinorOfSmoothMatrix
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_alphaOf : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaOf BM l H bp p) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hab hj hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p
  obtain ⟨hH, hbpc, hchart, hpt, -⟩ := hF
  intro w hw
  have hbw : bp w ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := (hpt w hw).1
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u)) w := by
    refine GlobalTheory.CompanionTheory.Ar.PB.CWeight.contDiffAt_blockPot j p.2 ?_ ?_ ?_ ?_
    · intro r s
      exact (GlobalTheory.T.base_chart_flag_analytic_map K ι Φ y Ψ N j M n d BM l p.1 Un bp hUn hbpc hchart
        (fun w' hw' => (hpt w' hw').1) r s).contDiffAt (hUn.mem_nhds hw)
    · intro r s
      exact (hH p.1 r s w hw).contDiffAt.restrict_scalars ℝ
    · exact (BM.G_pos l p.1 (bp w) hbw).2
    · exact ((hpt w hw).2 p.1).2
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) w := by
    by_cases hb : M.blk p = none
    · have hreg := ((BM.good l (bp w) hbw.1).2.2 p hb).2.1
      have han := GlobalTheory.T.regular_function_analytic_on_chart _ _ _ M.x ((BM.F l).υ p) d n BM.Rb Un bp w hUn hw hbpc hchart hreg
      have hne : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsVal BM l p (bp w) ≠ 0 :=
        GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l p (bp w) hbw.1 hb
      obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic d _ w han hne
      have hre0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Complex.reCLM (Hh z)) w :=
        Complex.reCLM.contDiff.contDiffAt.comp w (hHh.contDiffAt.restrict_scalars ℝ)
      have hre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (Hh z).re) w := by
        simpa using hre0
      refine hre.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      show GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp z) = (Hh z).re
      unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
      rw [if_pos hb]
      exact hz
    · have hz : (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) = fun _ => (0 : ℝ) := by
        funext u
        unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
        rw [if_neg hb]
      rw [hz]
      exact contDiffAt_const
  have he : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.alphaOf BM l H bp p = fun u =>
      GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u) -
        GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u) := rfl
  rw [he]
  exact (hA.sub hB).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
