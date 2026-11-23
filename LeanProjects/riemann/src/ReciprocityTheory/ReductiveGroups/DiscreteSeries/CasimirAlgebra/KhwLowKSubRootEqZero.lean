import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.RhoEqRhoCAddRhoN
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def wdP (ε : Fin n → Bool) (a b : Fin n) : Prop := (a < b ∧ ε a = ε b) ∨ (b < a ∧ ε a ≠ ε b)

instance signedOrder_decidable (ε : Fin n → Bool) : DecidableRel (wdP ε) := fun a b => by
  unfold wdP; infer_instance

theorem signedOrder_irrefl (ε : Fin n → Bool) (a : Fin n) : ¬ wdP ε a a := by simp [wdP]

theorem signedOrder_iff_not_swap_of_ne (ε : Fin n → Bool) (a b : Fin n) (h : a ≠ b) : wdP ε a b ↔ ¬ wdP ε b a := by
  unfold wdP
  rcases lt_or_gt_of_ne h with h | h
  · by_cases he : ε a = ε b
    · simp [h, lt_asymm h, he]
    · simp [h, lt_asymm h, he, Ne.symm he]
  · by_cases he : ε a = ε b
    · simp [h, lt_asymm h, he]
    · simp [h, lt_asymm h, he, Ne.symm he]

theorem wd_ind (ε : Fin n → Bool) (a b : Fin n) :
    ((if wdP ε a b then (1:ℝ) else 0) - (if wdP ε b a then (1:ℝ) else 0)) =
    ((if a < b ∧ ε b = ε a then (1:ℝ) else 0) - (if b < a ∧ ε b = ε a then 1 else 0)) -
    ((if a < b ∧ ε b ≠ ε a then (1:ℝ) else 0) - (if b < a ∧ ε b ≠ ε a then 1 else 0)) := by
  unfold wdP
  rcases lt_trichotomy a b with h | rfl | h
  · by_cases he : ε a = ε b
    · simp [h, lt_asymm h, he]
    · simp [h, lt_asymm h, he, Ne.symm he]
  · simp
  · by_cases he : ε a = ε b
    · simp [h, lt_asymm h, he]
    · simp [h, lt_asymm h, he, Ne.symm he]

theorem wd_card (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) = ∑ b, if p b then (1:ℝ) else 0 := by
  rw [Finset.sum_boole]

theorem wd_diag (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (μ a - μ b) = 2 * dot μ (rhoC ε - rhoN ε) := by
  have h1 : ∀ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (μ a - μ b) =
      ∑ b, (if wdP ε a b then μ a else 0) - ∑ b, (if wdP ε a b then μ b else 0) := by
    intro a; rw [sum_filter, ← sum_sub_distrib]
    exact sum_congr rfl (fun b _ => by split_ifs <;> simp)
  have h2 : ∑ a, ∑ b, (if wdP ε a b then μ b else 0) = ∑ a, ∑ b, (if wdP ε b a then μ a else 0) :=
    Finset.sum_comm
  rw [sum_congr rfl (fun a _ => h1 a), sum_sub_distrib, h2, ← sum_sub_distrib, dot, mul_sum]
  refine sum_congr rfl (fun a _ => ?_)
  rw [← sum_sub_distrib]
  have hk : ∀ b, (if wdP ε a b then μ a else 0) - (if wdP ε b a then μ a else 0) =
      μ a * ((if wdP ε a b then (1:ℝ) else 0) - (if wdP ε b a then (1:ℝ) else 0)) := by
    intro b; split_ifs <;> ring
  simp only [hk, wd_ind, ← mul_sum, sum_sub_distrib, Pi.sub_apply, rhoC, rhoN, wd_card]
  ring

theorem wd_offdiag (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (if b < a ∧ ε b ≠ ε a then f a b else 0) =
      ∑ a, ∑ b ∈ univ.filter (fun b => a < b ∧ ε a ≠ ε b), f b a := by
  have h2 : ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then f b a else 0) =
      ∑ a, ∑ b, (if b < a ∧ ε b ≠ ε a then f a b else 0) := Finset.sum_comm
  simp only [sum_filter]
  rw [h2]
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
  by_cases h : b < a ∧ ε b ≠ ε a
  · have hp : wdP ε a b := Or.inr ⟨h.1, Ne.symm h.2⟩
    simp [h, hp]
  · simp [h]

theorem nsq_add' (x y : Fin n → ℝ) : nsq (x + y) = nsq x + 2 * dot x y + nsq y := by
  simp only [nsq, dot, Pi.add_apply, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun _ _ => by ring)

theorem nsq_sub' (x y : Fin n → ℝ) : nsq (x - y) = nsq x - 2 * dot x y + nsq y := by
  simp only [nsq, dot, Pi.sub_apply, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl (fun _ _ => by ring)

theorem nsq_shift (μ x y : Fin n → ℝ) : nsq (μ + x - y) - nsq (x - y) = nsq μ + 2 * dot μ (x - y) := by
  simp only [nsq, dot, Pi.add_apply, Pi.sub_apply, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl (fun _ _ => by ring)

theorem nsq_root {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  simp [nsq, dot, root, Pi.single_apply, mul_sub, sum_sub_distrib, hab, Ne.symm hab]
  norm_num

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem wd_inner_self (x : M) : inner ℂ x x = ((‖x‖ : ℝ) : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K x

theorem wd_term (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v) {a b : Fin n} (hab : wdP ε a b) :
    inner ℂ v (E b a (E a b v)) = ((-(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0) : ℝ) : ℂ) := by
  rcases hab with ⟨h, he⟩ | ⟨h, he⟩
  · rw [hv.2 a b h he, map_zero, inner_zero_right]
    simp [lt_asymm h]
  · have h1 := hU a b v (E a b v)
    rw [adjSign, if_neg he, wd_inner_self] at h1
    rw [if_pos ⟨h, Ne.symm he⟩]
    push_cast
    linear_combination h1

theorem casimir_khw_identity (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v)
    {c : ℝ} (hc : casimir E v = (c : ℂ) • v) :
    c * ‖v‖ ^ 2 = (nsq (μ + rhoC ε - rhoN ε) - nsq (rhoC ε - rhoN ε)) * ‖v‖ ^ 2 -
      2 * ∑ a, ∑ b ∈ univ.filter (fun b => a < b ∧ ε a ≠ ε b), ‖E b a v‖ ^ 2 := by
  have hs := casimir_split hE (wdP ε) (signedOrder_irrefl ε) (signedOrder_iff_not_swap_of_ne ε)
  have h1 : inner ℂ v (casimir E v) = ((c * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hc, inner_smul_right, wd_inner_self]; push_cast; ring
  have hA : ∀ a, inner ℂ v (E a a (E a a v)) = (((μ a) ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [hv.1 a, map_smul, hv.1 a, inner_smul_right, inner_smul_right, wd_inner_self]
    push_cast; ring
  have hB : ∀ a b, wdP ε a b → inner ℂ v ((E a a - E b b + 2 • (E b a * E a b)) v) =
      (((μ a - μ b) * ‖v‖ ^ 2 + 2 * -(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0) : ℝ) : ℂ) := by
    intro a b hab
    rw [two_smul, LinearMap.add_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      inner_add_right, inner_add_right, inner_sub_right, hv.1 a, hv.1 b, inner_smul_right,
      inner_smul_right, wd_inner_self, wd_term ε hU hv hab]
    push_cast; ring
  have h2 : inner ℂ v (casimir E v) = ((∑ a, (μ a) ^ 2 * ‖v‖ ^ 2 +
      ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b),
        ((μ a - μ b) * ‖v‖ ^ 2 + 2 * -(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0)) : ℝ) : ℂ) := by
    rw [hs, LinearMap.add_apply, inner_add_right]
    simp only [LinearMap.sum_apply, inner_sum]
    push_cast
    congr 1
    · exact sum_congr rfl (fun a _ => by rw [Module.End.mul_apply, hA]; push_cast; ring)
    · refine sum_congr rfl (fun a _ => ?_)
      refine sum_congr rfl (fun b hb => ?_)
      rw [hB a b (mem_filter.1 hb).2]; push_cast; ring
  have h4 : c * ‖v‖ ^ 2 = ∑ a, (μ a) ^ 2 * ‖v‖ ^ 2 +
      ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b),
        ((μ a - μ b) * ‖v‖ ^ 2 + 2 * -(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0)) := by
    exact_mod_cast h1.symm.trans h2
  have e1 : ∑ a, (μ a) ^ 2 * ‖v‖ ^ 2 = nsq μ * ‖v‖ ^ 2 := by
    rw [nsq, dot, sum_mul]; exact sum_congr rfl (fun _ _ => by ring)
  have e2 : ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b),
        ((μ a - μ b) * ‖v‖ ^ 2 + 2 * -(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0)) =
      (∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (μ a - μ b)) * ‖v‖ ^ 2 -
        2 * ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b),
          (if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0) := by
    rw [sum_mul, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl (fun a _ => ?_)
    rw [sum_mul, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun b _ => by ring)
  rw [h4, e1, e2, wd_diag, wd_offdiag ε (fun a b => ‖E a b v‖ ^ 2), nsq_shift]
  ring

theorem casimir_khw_le (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v)
    (hv0 : v ≠ 0) {c : ℝ} (hc : casimir E v = (c : ℂ) • v) :
    c + nsq (rhoC ε - rhoN ε) ≤ nsq (μ + rhoC ε - rhoN ε) := by
  have h := casimir_khw_identity ε hE hU hv hc
  have hS : 0 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => a < b ∧ ε a ≠ ε b), ‖E b a v‖ ^ 2 :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
  have hpos : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv0) 2
  apply le_of_mul_le_mul_right _ hpos
  linarith

theorem khw_lowK_sub_root_eq_zero (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) (lam : Fin n → ℝ) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) (hgap : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b)) {v : M}
    (hv : IsKHWVec ε E (lowK ε lam - root a b) v)
    (hc : casimir E v = (casVal lam : ℂ) • v) : v = 0 := by
  by_contra hv0
  have hle := casimir_khw_le ε hE hU hv hv0 hc
  have hμ : lowK ε lam - root a b + rhoC ε - rhoN ε = lam - root a b := by
    ext i; simp only [lowK, Pi.add_apply, Pi.sub_apply]; ring
  rw [hμ] at hle
  have e1 := nsq_sub' lam (root a b)
  have e2 : nsq (root a b) = 2 := nsq_root (ne_of_lt hab)
  have e3 : casVal lam = nsq lam - (nsq (rhoC ε) + 2 * dot (rhoC ε) (rhoN ε) + nsq (rhoN ε)) := by
    rw [casVal, rho_eq_rhoC_add_rhoN ε, nsq_add']
  have e4 := nsq_sub' (rhoC ε) (rhoN ε)
  linarith

end Unitary

end ReciprocityTheory.ChartRestriction.DS
