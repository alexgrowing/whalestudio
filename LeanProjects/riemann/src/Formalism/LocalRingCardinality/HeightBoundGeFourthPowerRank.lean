import Formalism.LocalRingCardinality.DataParamsT
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

namespace Formalism.BasicNotions

theorem D7.eight_le_f (D : D7) : 8 ≤ D.R.f := by
  have h : 2 ≤ D.R.e := D.host.two_le_e
  have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) h
  have h5 : 2 ^ D.R.e ≤ D.R.ord := D.R.toFrame.two_pow_le_ord
  unfold Ranks.f Ranks.n
  omega

theorem ParamsT.t_ge_fourth_power_rank {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    128 * D.R.r ^ 4 ≤ D.R.t := by
  have hf := D.eight_le_f
  have h1 : D.R.f * D.R.r * (D.R.r + 1) ≤ T.nWn := T.nW_lo.1
  have h2 : 8 * D.R.r ^ 2 ≤ T.nWn := by
    refine le_trans ?_ h1
    calc 8 * D.R.r ^ 2 = 8 * D.R.r * D.R.r := by ring
      _ ≤ D.R.f * D.R.r * (D.R.r + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hf) (Nat.le_succ _)
  have h3 : 2 * T.nWn ≤ T.TO := by
    have := T.TO_nW
    have h' : 2 * T.nWn ≤ (T.Dp + 2) * T.nWn := Nat.mul_le_mul_right _ (by omega)
    omega
  have h4 : 128 * D.R.r ^ 4 ≤ T.TO * T.nWn := by
    calc 128 * D.R.r ^ 4 = (2 * (8 * D.R.r ^ 2)) * (8 * D.R.r ^ 2) := by ring
      _ ≤ (2 * T.nWn) * T.nWn := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h2
      _ ≤ T.TO * T.nWn := Nat.mul_le_mul_right _ h3
  have h5 : D.R.r ≤ T.nP := by
    rw [T.nP_eq]
    have : D.R.r ≤ 8 * D.R.f * D.R.r := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h6 := T.split
  omega

theorem ParamsT.t_ge_80 {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    80 * (D.R.r : ℝ) ^ ((7 : ℝ) / 2) ≤ (D.R.t : ℝ) := by
  have h : ((128 * D.R.r ^ 4 : ℕ) : ℝ) ≤ (D.R.t : ℝ) := by exact_mod_cast T.t_ge_fourth_power_rank
  push_cast at h
  rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
  · rw [h0]; simp
  · have h1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast h0
    have h2 : (D.R.r : ℝ) ^ ((7 : ℝ) / 2) ≤ (D.R.r : ℝ) ^ ((4 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    rw [Real.rpow_natCast] at h2
    have h3 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
    linarith

theorem ParamsT.two_rank_sq_lt_t {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (hr : 0 < D.R.r) :
    2 * D.R.r ^ 2 + 2 < D.R.t := by
  have h := T.t_ge_fourth_power_rank
  have h1 : D.R.r ^ 2 ≤ D.R.r ^ 4 := Nat.pow_le_pow_right hr (by norm_num)
  have h2 : 1 ≤ D.R.r ^ 2 := Nat.one_le_pow _ _ hr
  omega

theorem ParameterChoice'.m_sq_le_k {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : D.R.m ^ 2 ≤ D.R.k := by
  have h1 : (1 : ℝ) ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have h2 := P.k_ge_m2L
  have h3 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by positivity
  have h4 : (D.R.m : ℝ) ^ 2 ≤ (D.R.k : ℝ) := by nlinarith
  exact_mod_cast h4

theorem ParameterChoice'.three_q_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (j : ℕ) (hj : 1 ≤ j) :
    3 * (D.R.sigW j).2 + 1 ≤ D.R.r := by
  have h := P.m_sq_le_k
  have h2 := D.R.two_le_m
  have h3 : 2 * D.R.m ≤ D.R.m ^ 2 := by
    calc 2 * D.R.m ≤ D.R.m * D.R.m := Nat.mul_le_mul_right _ h2
      _ = D.R.m ^ 2 := by ring
  unfold Ranks.sigW Ranks.r
  simp only
  omega

def D7.NodeGap (D : D7) (h : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m),
    h ≤ (((D.hcW u τ).b ⟨j + 1, hj⟩ - (D.hcW u τ).b ⟨j, by omega⟩ : ℚ) : ℝ)

theorem D7.NodeGap.mono {D : D7} {h h' : ℝ} (H : D.NodeGap h) (hle : h' ≤ h) : D.NodeGap h' :=
  fun u τ j hj => le_trans hle (H u τ j hj)

theorem ParameterChoice'.nodeGap_ge_heightBound {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : D.NodeGap (LevelStarExponents.h0 L) := by
  intro u τ j hj
  rw [D.hcW_b u τ]
  exact (P.nodes_gap τ j hj).1

theorem ParameterChoice'.nodeGap_ge_cubic_rank {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) :
    D.NodeGap (4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6) :=
  P.nodeGap_ge_heightBound.mono P.h0_ge.2.2.2.2.1

theorem ParamsT.heightBound_ge_fourth_power_rank {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    256 * (D.R.r : ℝ) ^ 4 ≤ LevelStarExponents.h0 L := by
  have h1 : ((128 * D.R.r ^ 4 : ℕ) : ℝ) ≤ (D.R.t : ℝ) := by exact_mod_cast T.t_ge_fourth_power_rank
  push_cast at h1
  have h2 := P.h0_ge.2.2.2.2.1
  have h3 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  linarith

theorem ParamsT.nodeGap_ge_fourth_power_rank {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    D.NodeGap (256 * (D.R.r : ℝ) ^ 4) :=
  P.nodeGap_ge_heightBound.mono T.heightBound_ge_fourth_power_rank

end Formalism.BasicNotions
