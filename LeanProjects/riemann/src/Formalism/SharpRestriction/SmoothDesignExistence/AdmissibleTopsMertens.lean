import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSa
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSb
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
import Formalism.SharpRestriction.GrowthBounds.JointsLit

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

def TopsF {eps : ℝ} (Fm : FamP eps) : Prop := ChosenTT Fm ∧ ∃ Cb : ℝ, 0 < Cb ∧ ChosenBad Fm Cb

theorem topsF_of_chosenE {eps : ℝ} (Fm : FamP eps) {C0 CH : ℝ} (h : ChosenE Fm C0 CH) : TopsF Fm := by
  obtain ⟨C5, c6, Cb, -, -, hCb, -, hTT, hBad, -⟩ := h
  exact ⟨hTT, Cb, hCb, hBad⟩

private lemma sum_log_div_le_two_mul_mul_add_two (s : Finset ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hs : ∀ p ∈ s, 1 ≤ p ∧ p < ⌈Real.exp T⌉₊) :
    ∑ p ∈ s, Real.log p / p ≤ 2 * T * (T + 2) := by
  have hterm : ∀ p ∈ s, Real.log p / p ≤ T * (2 / ((p : ℝ) + 1)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hs p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h1
    have hp0 : (0 : ℝ) < p := by linarith
    have hpe : (p : ℝ) < Real.exp T := Nat.lt_ceil.1 h2
    have hlog : Real.log p ≤ T := by
      have h := Real.log_le_log hp0 hpe.le
      rwa [Real.log_exp] at h
    have e1 : Real.log p / p ≤ T / p := by gcongr
    have h3 : 1 / (p : ℝ) ≤ 2 / ((p : ℝ) + 1) := by
      first
      | (rw [div_le_div_iff₀ hp0 (by linarith)]; linarith)
      | (rw [div_le_div_iff hp0 (by linarith)]; linarith)
    have e2 : T / p ≤ T * (2 / ((p : ℝ) + 1)) := by
      calc T / p = T * (1 / p) := by ring
        _ ≤ T * (2 / ((p : ℝ) + 1)) := mul_le_mul_of_nonneg_left h3 hT
    linarith
  have hsub : s ⊆ Finset.range ⌈Real.exp T⌉₊ := fun p hp => Finset.mem_range.2 (hs p hp).2
  have hh : ∑ p ∈ Finset.range ⌈Real.exp T⌉₊, ((p : ℝ) + 1)⁻¹ = (harmonic ⌈Real.exp T⌉₊ : ℝ) := by
    first
    | simp [harmonic]
    | (rw [harmonic]; push_cast; rfl)
  have hlN : Real.log (⌈Real.exp T⌉₊ : ℝ) ≤ T + 1 := by
    rcases Nat.eq_zero_or_pos ⌈Real.exp T⌉₊ with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · have hN0 : (0 : ℝ) < (⌈Real.exp T⌉₊ : ℝ) := by exact_mod_cast h0
      have hE : (1 : ℝ) ≤ Real.exp T := Real.one_le_exp hT
      have hc := Nat.ceil_lt_add_one (Real.exp_pos T).le
      have hNle : (⌈Real.exp T⌉₊ : ℝ) ≤ 2 * Real.exp T := by linarith
      have h2 := Real.log_le_log hN0 hNle
      rw [Real.log_mul (by norm_num) (Real.exp_pos T).ne', Real.log_exp] at h2
      have hl2 : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      linarith
  calc ∑ p ∈ s, Real.log p / p ≤ ∑ p ∈ s, T * (2 / ((p : ℝ) + 1)) := Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ Finset.range ⌈Real.exp T⌉₊, T * (2 / ((p : ℝ) + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = 2 * T * ∑ p ∈ Finset.range ⌈Real.exp T⌉₊, ((p : ℝ) + 1)⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ 2 * T * (1 + Real.log (⌈Real.exp T⌉₊ : ℝ)) := by
        rw [hh]
        exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by positivity)
    _ ≤ 2 * T * (T + 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem admissible_tops_mertens {eps : ℝ} (Fm : FamP eps) (h : TopsF Fm) : G.Adm2F Fm := by
  obtain ⟨⟨xa, hTT⟩, Cb, hCb, xb, hBad⟩ := h
  unfold G.Adm2F G.Ev
  refine ⟨max (max xa xb) (max (Fm.x1 + 1) ((16 * Cb + 2) ^ (3 / eps))), fun x hx i => ?_⟩
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1' : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x := by linarith
  have hxc : (16 * Cb + 2) ^ (3 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hT1, hT2⟩ := hTT x hxa i
  have hB := hBad x hxb i
  unfold ChBad_at at hB
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hLe : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have he' : 0 < (Fm.L x i).sc.eps := (Fm.L x i).sc.eps_pos
  have he : 0 < eps := by rw [← hLe]; exact he'
  have hy1 : 1 < (Fm.L x i).sc.x := (Fm.L x i).sc.one_lt_alt
  have hy0 : 0 < (Fm.L x i).sc.x := by linarith
  have hT0 : 0 ≤ (Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3) := by positivity
  have hTbig : 16 * Cb + 2 ≤ (Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3) := by
    rw [hLx, hLe]
    have hc : (0 : ℝ) ≤ 16 * Cb + 2 := by linarith
    have hne : eps ≠ 0 := he.ne'
    have hm : 3 / eps * (eps / 3) = 1 := by
      first
      | (field_simp; ring)
      | field_simp
    calc 16 * Cb + 2 = ((16 * Cb + 2) ^ (3 / eps)) ^ (eps / 3) := by
          rw [← Real.rpow_mul hc, hm, Real.rpow_one]
      _ ≤ x ^ (eps / 3) := Real.rpow_le_rpow (by positivity) hxc (by positivity)
  have hS := sum_log_div_le_two_mul_mul_add_two (largeOrderResiduePrimes (Fm.L x i)) ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) hT0
    (fun p hp => by
      simp only [largeOrderResiduePrimes, Finset.mem_filter, Finset.mem_range] at hp
      exact ⟨hp.2.1.one_lt.le, hp.1⟩)
  have hBTT : AuxBlock8.BTT (Fm.D x i) (Fm.L x i) (Fm.Gx x i) ≤
      ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p * ((badTops (Fm.Gx x i) p).card : ℝ) := by
    unfold AuxBlock8.BTT
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [AuxBlock8.primesResidueBelow, largeOrderResiduePrimes, Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2.2, hp.2⟩
    · intro p _ _
      have hl : 0 ≤ Real.log (p : ℝ) := by
        rcases Nat.eq_zero_or_pos p with h0 | h0
        · simp [h0]
        · exact Real.log_nonneg (by exact_mod_cast h0)
      exact mul_nonneg (div_nonneg hl (Nat.cast_nonneg p)) (Nat.cast_nonneg _)
  have hdn : 0 ≤ (Fm.L x i).sc.delta1 * (Fm.D x i).R.n := by
    have hc0 : (0 : ℝ) ≤ ((Fm.D x i).host.TT.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hA : 0 < (Fm.L x i).sc.x ^ (-2 : ℝ) := by positivity
  have hpow : (Fm.L x i).sc.x ^ (-2 + (Fm.L x i).sc.eps) =
      (Fm.L x i).sc.x ^ (-2 : ℝ) * ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) ^ 3 := by
    have h3 : (Fm.L x i).sc.eps = (Fm.L x i).sc.eps / 3 * ((3 : ℕ) : ℝ) := by push_cast; ring
    rw [Real.rpow_add hy0, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le, ← h3]
  unfold AuxBlock8.adm2
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  rw [hpow]
  obtain ⟨T, hTe⟩ : ∃ T, T = (Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3) := ⟨_, rfl⟩
  obtain ⟨A, hAe⟩ : ∃ A, A = (Fm.L x i).sc.x ^ (-2 : ℝ) := ⟨_, rfl⟩
  rw [← hTe] at hS hTbig hT0 ⊢
  rw [← hAe] at hA hB ⊢
  have k1 : 16 * Cb * (T + 2) ≤ T ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hTbig hT0]
  have k2 := mul_le_mul_of_nonneg_left k1
    (div_nonneg (mul_nonneg (mul_nonneg hdn hA.le) hT0) (by norm_num : (0 : ℝ) ≤ 2))
  have k3 := mul_le_mul_of_nonneg_left hS
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * (Cb * A)) hdn)
  have k4 := mul_le_mul_of_nonneg_right hT1 (by positivity : (0 : ℝ) ≤ A * T ^ 3)
  linarith [hBTT, hB, k2, k3, k4]

end Formalism.MainNotions.Pk

end
