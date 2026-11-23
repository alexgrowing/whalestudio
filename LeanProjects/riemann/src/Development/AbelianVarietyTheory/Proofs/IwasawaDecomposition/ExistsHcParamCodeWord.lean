import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

def hcParamOfCodeWord (R : Ranks) (G b₀ h : ℕ) (hG : 2 ≤ G) (hh : R.t + 3 ≤ h)
    (c : Fin R.k → Bool) : HCParam R where
  u i := if i.1 = 0 then (G : ℚ) * (R.k - 1) + 1 / 2 else if i.1 = R.k - 1 then (G : ℚ) - 1 / 2
    else if c i then (G : ℚ) * (R.k - i.1) - 1 / 2 else (G : ℚ) * (R.k - 1 - i.1) + 1 / 2
  v i := (G : ℚ) * (R.k - 1 - i.1)
  b j := b₀ + 2 * h * j.1
  e j := b₀ + 2 * h * j.1 + h
  u_gt_v i := by
    have hG' : (2 : ℚ) ≤ G := by exact_mod_cast hG
    have hi := i.2
    dsimp only
    split_ifs with h0 h1 h2
    · rw [h0]; push_cast; linarith
    · omega
    · linarith
    · linarith
  v_gt_u i := by
    have hG' : (2 : ℚ) ≤ G := by exact_mod_cast hG
    have hi := i.2
    dsimp only
    rw [if_neg (Nat.succ_ne_zero i.1)]
    split_ifs with h1 h2
    · have hk : (R.k : ℚ) = (i.1 : ℚ) + 2 := by
        have : R.k = i.1 + 2 := by omega
        exact_mod_cast this
      rw [hk]; linarith
    · push_cast; linarith
    · push_cast; linarith
  u_last_gt h0 h1 := by
    have hG' : (2 : ℚ) ≤ G := by exact_mod_cast hG
    have hb : (0 : ℚ) ≤ b₀ := by positivity
    have hk := R.m_add_three_le_k
    have hne : R.k - 1 ≠ 0 := by omega
    simp only [if_neg hne, if_true]
    push_cast
    linarith
  gap_be j := by
    have hh' : (R.t : ℚ) + 3 ≤ h := by exact_mod_cast hh
    have ht : (0 : ℚ) ≤ R.t := by positivity
    linarith
  gap_eb j hj := by
    have hh' : (R.t : ℚ) + 3 ≤ h := by exact_mod_cast hh
    have ht : (0 : ℚ) ≤ R.t := by positivity
    push_cast
    linarith
  e_int j := ⟨b₀ + 2 * h * j.1 + h, by push_cast; ring⟩
  u_half i := by
    split_ifs
    · exact ⟨G * (R.k - 1), by push_cast; ring⟩
    · exact ⟨G - 1, by push_cast; ring⟩
    · exact ⟨G * (R.k - i.1) - 1, by push_cast; ring⟩
    · exact ⟨G * (R.k - 1 - i.1), by push_cast; ring⟩
  v_int i := ⟨G * (R.k - 1 - i.1), by push_cast; ring⟩
  b_int j := ⟨b₀ + 2 * h * j.1, by push_cast; ring⟩

theorem exists_hcParam_codeWord : ∀ (R : Ranks) (G b₀ h : ℕ), 2 ≤ G → R.t + 3 ≤ h → ∃ P : (Fin R.k → Bool) → HCParam R, (∀ c i, (P c).v i = (G : ℚ) * (R.k - 1 - i.1)) ∧ (∀ c j, (P c).b j = b₀ + 2 * h * j.1) ∧ (∀ c j, (P c).e j = b₀ + 2 * h * j.1 + h) ∧ (∀ c (i : Fin R.k), (P c).u i = if i.1 = 0 then (G : ℚ) * (R.k - 1) + 1 / 2 else if i.1 = R.k - 1 then (G : ℚ) - 1 / 2 else if c i then (G : ℚ) * (R.k - i.1) - 1 / 2 else (G : ℚ) * (R.k - 1 - i.1) + 1 / 2) :=
  fun R G b₀ h hG hh =>
    ⟨hcParamOfCodeWord R G b₀ h hG hh, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩

end GlobalTheory
