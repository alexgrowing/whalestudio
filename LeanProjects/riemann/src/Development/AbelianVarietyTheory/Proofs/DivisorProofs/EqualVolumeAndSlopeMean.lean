import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeMeanOfSlopesMean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLimitAtZeroStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4

theorem two_le_weight_threshold {D : D7} (Y : ShimX D.what₂.Tau) (hf : 2 < D.R.f * (Y.N - 1)) {u : Wt Y} {g : ℝ}
    (hu : WeightHyp Y u g) : 2 ≤ bigB0 Y u g := by
  have h1 : 1 ≤ D.R.f := by
    rcases Nat.eq_zero_or_pos D.R.f with h | h
    · rw [h] at hf; omega
    · exact h
  have h2 : 1 ≤ Y.N := by have := Y.j_lt; omega
  have h1' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast h1
  have h2' : (1 : ℝ) ≤ Y.N := by exact_mod_cast h2
  have h3 : 0 ≤ supAbs Y u := Real.iSup_nonneg fun x => abs_nonneg _
  have h4 : 0 ≤ supAbs Y u / g := div_nonneg h3 hu.1.le
  have h5 : (1 : ℝ) ≤ (Y.N : ℝ) ^ 2 := one_le_pow₀ h2'
  have h6 : (1 : ℝ) ≤ (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le h1' h5
  have h7 : (1 : ℝ) ≤ (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 * (1 + supAbs Y u / g) :=
    one_le_mul_of_one_le_of_one_le h6 (by linarith)
  unfold bigB0
  linarith

theorem volEq_and_slopeMean : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), ∀ (Φ : ℝ → Fn Y) (C : ℝ),
    2 < D.R.f * (Y.N - 1) → LimFam Φ → PolySize A Φ → Agree A → Degrees A → EqVol A → Propor Y → Lower Φ C →
    GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.VolEq Y ∧ GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.SlopeMean Y C := by
  intro D Y A Φ C hf hLim hPoly hAg hDeg hEq hProp hLow
  obtain ⟨hw, hvol, -, hgeo⟩ := hDeg
  have hrat : ∀ u : D.what₂.Tau → Fin Y.N → ℚ, IsRat Y (GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.realWt Y u) :=
    fun u τ i => ⟨u τ i, rfl⟩
  refine ⟨⟨A.w, ⟨hw, hvol, fun u g hu c => ?_⟩, hEq⟩, fun u g hu => ?_⟩
  · convert hgeo _ (two_le_weight_threshold Y hf hu) _ (hrat u) c
  set v := GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.realWt Y u with hv
  have hB := two_le_weight_threshold Y hf hu
  set B := bigB0 Y v g with hBdef
  have hfd : 0 < flagDeg D.what₂.Tau Y.N v := GlobalTheory.SlopeCompare.flagDeg_pos hu.2.1
  obtain ⟨c₀⟩ := Y.compNe
  have hn : (0 : ℝ) < Fintype.card Y.Comp := by exact_mod_cast Fintype.card_pos
  have hvol' : Y.vol = Fintype.card Y.Comp * A.w c₀ := by
    rw [hvol, Finset.sum_congr rfl fun c _ => hEq c c₀]
    simp
  have hg : geoDeg Y v = Fintype.card Y.Comp * A.w c₀ * flagDeg D.what₂.Tau Y.N v := by
    rw [geoDeg, hProp, hvol']; rfl
  have hw₀ := hw c₀
  have hgpos : 0 < geoDeg Y v := by rw [hg]; positivity
  have hd : (0 : ℝ) < (dimY Y : ℝ) + 1 := by positivity
  obtain ⟨_, hP⟩ := hPoly
  have hsum := (hP B hB).2 v
  have hmean : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.compMean Y
      (fun c => evS Y (A.Ps B c) v 0 / (((dimY Y : ℝ) + 1) * (A.w c₀ * flagDeg D.what₂.Tau Y.N v))) =
      atWt Y (Φ B) v / (((dimY Y : ℝ) + 1) * geoDeg Y v) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.compMean, ← Finset.sum_div, hsum, hg]
    field_simp
  refine ⟨_, fun c => ?_, ⟨Φ B, hLim B hB, hgpos, hmean⟩, ?_⟩
  · have h1 := GlobalTheory.T.self_intersection_limit_at_zero D Y A hAg B hB v (hrat u) hu.2.1 c
    have h2 := hgeo B hB v (hrat u) c
    rw [hEq c c₀] at h2
    exact h1.div (h2.const_mul _) (by positivity)
  · rw [hmean, le_div_iff₀ (by positivity)]
    have h := hLow v g hu
    refine le_trans (le_of_eq ?_) h
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.errTerm, lg]
    ring

end GlobalTheory.Mean4
