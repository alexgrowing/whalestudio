import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellIntegralTopDensityEqLevelZeroStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroCutoffEqBigCellIntegralStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffEventuallyEqSmoothCoefficientStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem levelZeroForm_cutoff_tendsto_of_domination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (Y : Finset ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → (∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c)) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (p.RR f 0 w [] []).re) := by
  intro hX hP Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.levelZero_cutoff_eq_bigCell_integral hP Cb
  obtain ⟨C2, h2⟩ := GlobalTheory.T.bigCell_integral_topDensity_eq_levelZero hX hP Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N Y hD hχ hf hA hC hdom w hw hN
  have hpos : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 := by positivity
  have hpos' : (0 : ℝ) ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by
    positivity
  have hC1 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hpos) hpos') hC
  have hC2 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hpos) hpos') hC
  have hd := hdom w hw hN
  have hid := h2 Wp Wq P p f χ A N w hD hχ hf hA hC2 hw.1 hN hd
  have hform := h1 Wp Wq P p f χ A N w hD hχ hf hA hC1 hw.1 hN
  have hptw := GlobalTheory.T.topDensity_cutoff_eventually_eq_smoothCoefficient Wp Wq P p Cb f χ w hD hχ hf hw.1
  obtain ⟨hm, h, hi, hb⟩ := hd
  have key := tendsto_integral_filter_of_dominated_convergence h hm hb hi
    (hptw.mono fun c hc => tendsto_const_nhds.congr' (hc.mono fun _ e => e.symm))
  rw [hid] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hform ε hε).symm

end GlobalTheory
