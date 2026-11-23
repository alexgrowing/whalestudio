import Formalism.SizeWindowBrackets.GrowthBracketBoundOfSizeWindows
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma
import Formalism.SizeWindowBrackets.ChainSlopeWindows.CorollaryModelSideCondition
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedMeanLemmaNeedsDegree

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.CosetIndexLemmas

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

open Formalism.LFunctionChainParameters.DeficitSplitLemmas in
theorem rounding_rd_holds : RoundingRd := by
  classical
  intro ι W pr l sg sg' R X'' g₁ g₂ T hl hunit h1 h0 hR hX hg1 hg2 hT

  have s1 : ∑ w ∈ W, 2 * l w * (sg w - sg' w) ≤ ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w := by
    rw [← Finset.sum_filter_add_sum_filter_not W (fun w => pr w ∈ R)]
    have hA : ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w * (sg w - sg' w)
        ≤ ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w := by
      refine Finset.sum_le_sum fun w hw => ?_
      have hw' := (Finset.mem_filter.1 hw).1
      nlinarith [hl w hw', h1 w hw']
    have hB : ∑ w ∈ W.filter (fun w => ¬ pr w ∈ R), 2 * l w * (sg w - sg' w) ≤ 0 := by
      refine Finset.sum_nonpos fun w hw => ?_
      have hw' := Finset.mem_filter.1 hw
      nlinarith [hl w hw'.1, h0 w hw'.1 hw'.2]
    linarith

  have s2 : ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w = ∑ p ∈ R, 2 * Real.log p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := W.filter (fun w => pr w ∈ R)) (t := R) (g := pr)
      (fun w hw => (Finset.mem_filter.1 hw).2)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hunit p hp, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, _⟩, he⟩; exact ⟨hw, he⟩
    · rintro ⟨hw, he⟩; exact ⟨⟨hw, he ▸ hp⟩, he⟩

  have s3 : ∑ p ∈ R, 2 * Real.log p ≤ (2 * Real.log 4 + 6) * X'' := by
    rw [← Finset.sum_filter_add_sum_filter_not R (fun p : ℕ => (p : ℝ) ≤ X'')]
    have hA : ∑ p ∈ R.filter (fun p : ℕ => (p : ℝ) ≤ X''), 2 * Real.log p ≤ 2 * (Real.log 4 * X'') := by
      rw [← Finset.mul_sum]
      have := theta_finite X'' (R.filter (fun p : ℕ => (p : ℝ) ≤ X'')) hX (fun p hp =>
        ⟨(hR p (Finset.mem_filter.1 hp).1).1, (Finset.mem_filter.1 hp).2⟩)
      linarith
    have hnn : ∀ j : ℕ, 0 ≤ Real.log (j : ℝ) := fun j => Real.log_natCast_nonneg j
    have hB : ∑ p ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X''), 2 * Real.log p
        ≤ 2 * Real.log g₁ + 2 * Real.log g₂ + 2 * Real.log T := by
      have hle : ∀ p ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X''), 2 * Real.log (p : ℝ)
          ≤ (if p = g₁ then 2 * Real.log (g₁ : ℝ) else 0) + (if p = g₂ then 2 * Real.log (g₂ : ℝ) else 0)
            + (if p = T then 2 * Real.log (T : ℝ) else 0) := by
        intro p hp
        have hp' := Finset.mem_filter.1 hp
        have nn : ∀ (P : Prop) [Decidable P] (c : ℝ), 0 ≤ c → 0 ≤ (if P then c else 0) := by
          intro P _ c hc; split_ifs <;> [exact hc; exact le_refl _]
        have n1 := nn (p = g₁) (2 * Real.log (g₁ : ℝ)) (by linarith [hnn g₁])
        have n2 := nn (p = g₂) (2 * Real.log (g₂ : ℝ)) (by linarith [hnn g₂])
        have n3 := nn (p = T) (2 * Real.log (T : ℝ)) (by linarith [hnn T])
        rcases (hR p hp'.1).2 with h | h | h | h
        · exact absurd h hp'.2
        · have e : (if p = g₁ then 2 * Real.log (g₁ : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
        · have e : (if p = g₂ then 2 * Real.log (g₂ : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
        · have e : (if p = T then 2 * Real.log (T : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
      have m1 : ∀ (c : ℝ) (P : Prop) [Decidable P], 0 ≤ c → (if P then c else 0) ≤ c := by
        intro c P _ hc; split_ifs <;> [exact le_refl _; exact hc]
      have := m1 (2 * Real.log (g₁ : ℝ)) (g₁ ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn g₁])
      have := m1 (2 * Real.log (g₂ : ℝ)) (g₂ ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn g₂])
      have := m1 (2 * Real.log (T : ℝ)) (T ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn T])
      linarith
    linarith
  linarith

open Filter Asymptotics in
theorem ev_exp (A B κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x, x₀ ≤ x → A * x ^ B ≤ Real.exp (κ * x ^ δ) := by
  have hc : 0 < κ / (2 * (|B| + 1)) := by positivity
  have hb := (isLittleO_log_rpow_atTop hδ).bound hc
  have h2 := (tendsto_rpow_atTop hδ).eventually_ge_atTop (2 * |A| / κ)
  obtain ⟨x₀, hx₀⟩ := (hb.and h2).exists_forall_of_atTop
  refine ⟨max x₀ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hxd : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le _
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0, abs_of_nonneg hxd] at h1
  have hA : |A| ≤ κ * x ^ δ / 2 := by
    rw [div_le_iff₀ hκ] at h2; linarith
  have hB : B * Real.log x ≤ κ * x ^ δ / 2 := by
    have hB1 : B * Real.log x ≤ |B| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self B) hl0
    have hB2 : |B| * Real.log x ≤ (|B| + 1) * (κ / (2 * (|B| + 1)) * x ^ δ) := by
      apply mul_le_mul (by linarith) h1 hl0 (by positivity)
    have hB3 : (|B| + 1) * (κ / (2 * (|B| + 1)) * x ^ δ) = κ * x ^ δ / 2 := by
      field_simp
    linarith
  have hxB : x ^ B = Real.exp (B * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  have hxB0 : 0 < x ^ B := Real.rpow_pos_of_pos hx0 _
  calc A * x ^ B ≤ |A| * x ^ B := mul_le_mul_of_nonneg_right (le_abs_self A) hxB0.le
    _ ≤ Real.exp |A| * x ^ B := by
        apply mul_le_mul_of_nonneg_right _ hxB0.le
        have := Real.add_one_le_exp |A|; linarith
    _ = Real.exp (|A| + B * Real.log x) := by rw [hxB, Real.exp_add]
    _ ≤ Real.exp (κ * x ^ δ) := Real.exp_le_exp.2 (by linarith)

theorem sigma_window_eventual : SgWindowEv := by
  intro ε cH C1 e hε hC1
  obtain ⟨x1, hx1, h1⟩ := ev_exp (8 * (C1 + 1) ^ 2) (e + 2 * cH) (1 / 2) ε (by norm_num) hε
  obtain ⟨x2, hx2, h2⟩ := ev_exp 16 cH 1 (ε / 8) one_pos (by positivity)
  refine ⟨max x1 x2, ?_⟩
  intro x f m T de e0 hx hf hm hT hlT hde he0
  have hxa := h1 x (le_trans (le_max_left _ _) hx)
  have hxb := h2 x (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := by linarith [le_trans (le_max_left x1 x2) hx]
  have hS : 0 < x ^ (-cH) := Real.rpow_pos_of_pos hx0 _
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _

  have hTexp : Real.exp (1 / 2 * x ^ ε) ≤ T := by
    rw [← Real.le_log_iff_exp_le hT]
    nlinarith
  have hEpos : 0 < Real.exp (1 / 2 * x ^ ε) := Real.exp_pos _

  set y := x ^ (-cH) / (2 * (C1 + 1)) with hy
  have hy0 : 0 < y := by positivity
  have hxE : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have hsplit : x ^ (e + 2 * cH) = x ^ e / (x ^ (-cH)) ^ 2 := by
    rw [Real.rpow_add hx0, ← Real.rpow_natCast (x ^ (-cH)) 2, ← Real.rpow_mul hx0.le, div_eq_mul_inv,
      ← Real.rpow_neg hx0.le]
    congr 2; push_cast; ring
  have hde2 : de ≤ y ^ 2 := by
    have a1 : 2 * f / T ≤ 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) := by
      calc 2 * f / T ≤ 2 * x ^ e / T := by gcongr
        _ ≤ 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) := by gcongr
    have a2 : 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) ≤ y ^ 2 := by
      rw [div_le_iff₀ hEpos]
      have : y ^ 2 * (8 * (C1 + 1) ^ 2 * x ^ (e + 2 * cH)) = 2 * x ^ e := by
        rw [hsplit, hy]; field_simp; ring
      calc 2 * x ^ e = y ^ 2 * (8 * (C1 + 1) ^ 2 * x ^ (e + 2 * cH)) := this.symm
        _ ≤ y ^ 2 * Real.exp (1 / 2 * x ^ ε) := mul_le_mul_of_nonneg_left hxa (by positivity)
    linarith
  have hsq : Real.sqrt de ≤ y := Real.sqrt_le_iff.2 ⟨hy0.le, hde2⟩
  have p1 : C1 * Real.sqrt de ≤ x ^ (-cH) / 2 := by
    calc C1 * Real.sqrt de ≤ C1 * y := mul_le_mul_of_nonneg_left hsq hC1
      _ ≤ (C1 + 1) * y := by nlinarith
      _ = x ^ (-cH) / 2 := by rw [hy]; field_simp

  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]; norm_num
  have p2 : 4 * Real.sqrt (2 * e0) ≤ x ^ (-cH) / 2 := by
    rw [Real.sqrt_mul (by norm_num)]
    have b1 : Real.sqrt 2 * Real.sqrt e0 ≤ 2 * Real.exp (-(x ^ (ε / 8))) :=
      mul_le_mul hs2 he0 (Real.sqrt_nonneg _) (by norm_num)
    have b2 : 16 * Real.exp (-(x ^ (ε / 8))) ≤ x ^ (-cH) := by
      rw [Real.exp_neg, Real.rpow_neg hx0.le]
      have hc0 : 0 < x ^ cH := Real.rpow_pos_of_pos hx0 _
      have he0' : 0 < Real.exp (x ^ (ε / 8)) := Real.exp_pos _
      rw [one_mul] at hxb
      rw [← div_eq_mul_inv, div_le_iff₀ he0', ← div_eq_inv_mul, le_div_iff₀ hc0]
      exact hxb
    linarith
  linarith

open Filter in
theorem deletion_eventual_holds : DelEv := by
  intro ε hε
  obtain ⟨x₀, hx₀⟩ := ((tendsto_rpow_atTop (show 0 < ε / 7 by positivity)).eventually_ge_atTop 6).exists_forall_of_atTop
  refine ⟨x₀, fun x del hx hdel => ?_⟩
  have h6 := hx₀ x hx
  refine hdel.trans ?_
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := Real.add_one_le_exp (x ^ (ε / 7))
  norm_num
  linarith

open Formalism.LFunctionChainParameters.LErr in
theorem round_window_eventual : RoundWindowEv := by
  intro ε c hε hc
  obtain ⟨x1, hx1, h1⟩ := ev_exp c ((1 : ℝ) / 2 + ε / 2 + ε) 1 (ε / 3) one_pos (by positivity)
  refine ⟨x1, fun x m n hx hm hn => ?_⟩
  have hxa := h1 x hx
  have hx1' : 1 ≤ x := le_trans hx1 hx
  have hx0 : 0 < x := by linarith
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hX : XppTx x ε n = x * n * Real.exp (x ^ (ε / 3)) := by
    unfold XppTx wppTx bpTx aTx XpTx bTx
    have := Real.exp_pos (x ^ ε)
    have := Real.exp_pos (x ^ (ε / 3))
    have hn0 : 0 < n := by linarith
    field_simp
  rw [hX]
  have hE : 0 < Real.exp (x ^ (ε / 3)) := Real.exp_pos _
  rw [one_mul] at hxa
  calc c * m * x ^ ε ≤ c * x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε := by gcongr
    _ = c * x ^ ((1 : ℝ) / 2 + ε / 2 + ε) := by rw [mul_assoc, ← Real.rpow_add hx0]
    _ ≤ Real.exp (x ^ (ε / 3)) := hxa
    _ ≤ x * n * Real.exp (x ^ (ε / 3)) := by
        have : 1 ≤ x * n := by nlinarith
        nlinarith

end Formalism.LFunctionChainParameters.CosetIndexLemmas
