import Mathlib

namespace GlobalTheory.NormEvalSubBound

open Polynomial

section
variable {C : Type} [NormedField C] [IsUltrametricDist C]

lemma norm_pow_sub_pow_le {y a : C} (hy : ‖y‖ ≤ 1) (ha : ‖a‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - a ^ i‖ ≤ ‖y - a‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - a ^ (i + 1) = y * (y ^ i - a ^ i) + (y - a) * a ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - a‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - a‖ * ‖a‖ ^ i ≤ ‖y - a‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ha) (norm_nonneg _)
        _ = ‖y - a‖ := mul_one _

lemma norm_eval_sub_le (Q : C[X]) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {y a : C} (hy : ‖y‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) : ‖Q.eval y - Q.eval a‖ ≤ ‖y - a‖ := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖Q.coeff i‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
        mul_le_mul (hc i) (norm_pow_sub_pow_le hy ha i) (norm_nonneg _) zero_le_one
    _ = ‖y - a‖ := one_mul _

lemma norm_le_one_of_root (Q : C[X]) (hm : Q.Monic) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {a : C}
    (h : Q.eval a = 0) : ‖a‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  set n := Q.natDegree
  have hpos : 0 < ‖a‖ := lt_trans zero_lt_one hlt
  have hs : ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ ≤ ‖a‖ ^ n / ‖a‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' : i + 1 ≤ n := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    calc ‖Q.coeff i‖ * ‖a‖ ^ i * ‖a‖ ≤ 1 * ‖a‖ ^ i * ‖a‖ := by
          gcongr
          exact hc i
      _ = ‖a‖ ^ (i + 1) := by ring
      _ ≤ ‖a‖ ^ n := pow_le_pow_right₀ hlt.le hi'
  have hlt2 : ‖a‖ ^ n / ‖a‖ < ‖a‖ ^ n := div_lt_self (by positivity) hlt
  have he : Q.eval a = a ^ n + ∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by
    conv_lhs => rw [hm.as_sum]
    simp [eval_finset_sum, n]
  rw [h] at he
  have : a ^ n = -∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by linear_combination -he
  have h3 : ‖a‖ ^ n = ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ := by
    rw [← norm_pow, this, norm_neg]
  linarith
end

theorem main_theorem : (let d1 : {C : Type} → [inst : NormedField C] → [IsUltrametricDist C] → Subfield C → Subring C := @(fun {C : Type} [NormedField C] [IsUltrametricDist C] (F : Subfield C) ↦ Subfield.toSubring F ⊓ Valuation.integer NormedField.valuation); ∀ {C : Type} [inst : NormedField C] [inst_1 : IsUltrametricDist C] {F : Subfield C} [IsAlgClosed C] [inst_3 : IsLocalRing ↥(d1 F)], (∀ (x : C), ‖x‖ ≤ (1 : ℝ) → ∃ y ∈ F, ‖x - y‖ < (1 : ℝ)) → IsAlgClosed (IsLocalRing.ResidueField ↥(d1 F))) := by
  intro d1 C _ _ F _ _ hdense
  have mem : ∀ x : C, x ∈ d1 F ↔ x ∈ F ∧ ‖x‖ ≤ 1 := by
    intro x
    simp only [d1, Subring.mem_inf, Subfield.mem_toSubring, Valuation.mem_integer_iff,
      NormedField.valuation_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
  apply IsAlgClosed.of_exists_root
  intro p hmon hirr
  have hlift : p ∈ lifts (IsLocalRing.residue (d1 F)) :=
    (mem_lifts p).mpr (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_degree_eq_and_monic hlift hmon
  set Q : C[X] := q.map (d1 F).subtype with hQ
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    rw [hQ, coeff_map]; exact ((mem _).mp (q.coeff i).2).2
  have hQm : Q.Monic := hqmon.map _
  have hQdeg : Q.degree ≠ 0 := by
    rw [hQ, degree_map_eq_of_injective (Subring.subtype_injective _), hqdeg]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root Q hQdeg
  have ha1 : ‖a‖ ≤ 1 := norm_le_one_of_root Q hQm hQc ha
  obtain ⟨y, hyF, hya⟩ := hdense a ha1
  have hy1 : ‖y‖ ≤ 1 := by
    have : y = a - (a - y) := by ring
    rw [this]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 ?_)
    rw [norm_neg]; exact hya.le
  let y' : d1 F := ⟨y, (mem y).mpr ⟨hyF, hy1⟩⟩
  refine ⟨IsLocalRing.residue _ y', ?_⟩
  rw [← hqmap, eval_map, eval₂_hom, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hval : ((q.eval y' : d1 F) : C) = Q.eval y := by
    rw [hQ, eval_map]
    exact (eval₂_hom (d1 F).subtype y').symm
  have hn : ‖((q.eval y' : d1 F) : C)‖ < 1 := by
    rw [hval]
    have : Q.eval y = Q.eval y - Q.eval a := by rw [IsRoot.def.mp ha, sub_zero]
    rw [this]
    refine lt_of_le_of_lt (norm_eval_sub_le Q hQc hy1 ha1) ?_
    rwa [norm_sub_rev]
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  have h1 : ((q.eval y' : d1 F) : C) * (v : C) = 1 := by
    have := congrArg Subtype.val huv
    simpa using this
  have hv : ‖(v : C)‖ ≤ 1 := ((mem _).mp v.2).2
  have : ‖((q.eval y' : d1 F) : C) * (v : C)‖ < 1 := by
    rw [norm_mul]
    calc _ ≤ ‖((q.eval y' : d1 F) : C)‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hn
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

end GlobalTheory.NormEvalSubBound
