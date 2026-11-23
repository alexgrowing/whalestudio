import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_window : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C →
    L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ (bHat L : ℝ) ∧
      (bHat L : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1 := by
  intro D L C h
  obtain ⟨hC, _, hw, hwb, -, hb⟩ := h
  obtain ⟨s, hs⟩ := D.R.t_odd
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hts : ((D.R.t : ℝ) + 1) / 2 = (s : ℝ) + 1 := by
    rw [hs]; push_cast; ring
  have hb'pos : 0 < L.sc.b' := by
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hfac : (1 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb' : L.sc.b' ≤ L.sc.b := by nlinarith
  have htb : (D.R.t : ℝ) + 2 ≤ L.sc.b := by
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hdiv : (D.R.t + 1) / 2 = s + 1 := by omega
  have hb0 : 0 ≤ L.sc.b := by linarith
  have hc1 := Nat.le_ceil L.sc.b
  have hc2 := Nat.ceil_lt_add_one hb0
  have hle : s + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((s + 1 : ℕ) : ℝ) ≤ ⌈L.sc.b⌉₊ := by
      have : (D.R.t : ℝ) = 2 * s + 1 := by rw [hs]; push_cast; ring
      push_cast; nlinarith
    exact_mod_cast this
  have hval : (bHat L : ℝ) = (⌈L.sc.b⌉₊ : ℝ) - ((s : ℝ) + 1) := by
    unfold bHat
    rw [hdiv, Nat.cast_sub hle]
    push_cast; ring
  rw [hval, hts]
  constructor <;> linarith

end GlobalTheory.HTW
