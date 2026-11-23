import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwA
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLie

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem long_weyl_element_apply (i j : Fin (2 * r + k + 1)) : w0B k r i j = if i = tau k r j then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold w0B bigCell
  by_cases h1 : j.val < r
  · rw [dif_pos h1]
    have e : (esI k r ⟨j.val, h1⟩ = i) ↔ (i = tau k r j) := by
      constructor
      · intro h; apply Fin.ext; rw [← h]; simp [esI, tau, h1]
      · intro h; apply Fin.ext; rw [h]; simp [esI, tau, h1]
    by_cases h : i = tau k r j
    · rw [if_pos (e.2 h).symm, if_pos h]; rfl
    · rw [if_neg (fun h' => h (e.1 h'.symm)), if_neg h]
  · rw [dif_neg h1]
    by_cases h2 : j.val ≤ r + k
    · rw [dif_pos h2]
      have htj : tau k r j = j := by apply Fin.ext; simp [tau]; omega
      by_cases hi2 : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi2, htj, Matrix.one_apply]
        by_cases h : i = j
        · rw [if_pos (by subst h; rfl), if_pos h]
        · rw [if_neg (fun h' => h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))), if_neg h]
      · rw [dif_neg hi2, htj, if_neg]
        intro h; apply hi2; rw [h]; exact ⟨by omega, h2⟩
    · rw [dif_neg h2]
      have htj : (tau k r j).val = 2 * r + k - j.val := by simp [tau]; omega
      by_cases h : i.val = 2 * r + k - j.val
      · rw [if_pos h, if_pos (Fin.ext (by rw [htj]; exact h))]; simp
      · rw [if_neg h, if_neg (fun h' => h (by rw [h', htj]))]

theorem w0Sq : LongWeylElementSquare := by
  intro k r
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]
  · rw [long_weyl_element_apply, long_weyl_element_apply, if_pos rfl, mul_one, Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos (by rw [h, tau_tau]), if_pos h]
    · rw [if_neg (fun h' => h (by rw [h', tau_tau])), if_neg h]
  · intro m _ hm
    rw [long_weyl_element_apply m j, if_neg hm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem adjoint_long_weyl_element : adjH (w0B k r) = w0B k r := by
  have h1 : adjH (w0B k r) * w0B k r = 1 := (mem_UH_iff _).1 long_weyl_element_mem
  calc adjH (w0B k r) = adjH (w0B k r) * (w0B k r * w0B k r) := by rw [w0Sq k r, Matrix.mul_one]
    _ = (adjH (w0B k r) * w0B k r) * w0B k r := by rw [Matrix.mul_assoc]
    _ = w0B k r := by rw [h1, Matrix.one_mul]

theorem longestWeylElementGL_conj_apply_rev (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (w0B k r * M * w0B k r) i j = M (tau k r i) (tau k r j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]
  · rw [long_weyl_element_apply (tau k r j) j, if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
    · rw [long_weyl_element_apply, if_pos (tau_tau i).symm, one_mul]
    · intro m _ hm
      rw [long_weyl_element_apply, if_neg (fun h => hm (by rw [h, tau_tau])), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro m _ hm
    rw [long_weyl_element_apply m j, if_neg hm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end Formalism.L2.SG.Pf.BH.Sw

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

instance decMid (i : Fin (2 * r + k + 1)) : Decidable (Mid k r i) := by unfold Mid; infer_instance

theorem mid_iff (i : Fin (2 * r + k + 1)) : Mid k r i ↔ dg k r i = r := by
  have := i.isLt
  unfold Mid dg; split_ifs <;> omega

theorem dg_inj {i j : Fin (2 * r + k + 1)} (h : dg k r i = dg k r j) (hm : ¬ Mid k r i) : i = j := by
  have := i.isLt; have := j.isLt
  rw [mid_iff] at hm
  apply Fin.ext
  unfold dg at h hm; split_ifs at h hm <;> omega

theorem mid_tau (i : Fin (2 * r + k + 1)) : Mid k r (tau k r i) ↔ Mid k r i := by
  rw [mid_iff, mid_iff, dg_tau]; have := dg_le (k := k) (r := r) i; omega

def posP (Y : Mat k r) : Mat k r := fun i j => if dg k r i < dg k r j then Y i j else 0

def negP (Y : Mat k r) : Mat k r := fun i j => if dg k r j < dg k r i then Y i j else 0

def middlePart (Y : Mat k r) : Mat k r := fun i j => if Mid k r i ∧ Mid k r j then Y i j else 0

def xOf (Y : Mat k r) (a : Fin r) : ℂ := Y (eI k r a) (eI k r a)

theorem adjH_posP (Y : Mat k r) : adjH (posP Y) = posP (adjH Y) := by
  ext i j
  rw [adjH_apply]
  unfold posP
  have hi := dg_le (k := k) (r := r) i; have hj := dg_le (k := k) (r := r) j
  by_cases h : dg k r i < dg k r j
  · rw [if_pos (by rw [dg_tau, dg_tau]; omega), if_pos h, adjH_apply]
  · rw [if_neg (by rw [dg_tau, dg_tau]; omega), if_neg h, star_zero, mul_zero, zero_mul]

theorem adjH_negP (Y : Mat k r) : adjH (negP Y) = negP (adjH Y) := by
  ext i j
  rw [adjH_apply]
  unfold negP
  have hi := dg_le (k := k) (r := r) i; have hj := dg_le (k := k) (r := r) j
  by_cases h : dg k r j < dg k r i
  · rw [if_pos (by rw [dg_tau, dg_tau]; omega), if_pos h, adjH_apply]
  · rw [if_neg (by rw [dg_tau, dg_tau]; omega), if_neg h, star_zero, mul_zero, zero_mul]

theorem adjH_midP (Y : Mat k r) : adjH (middlePart Y) = middlePart (adjH Y) := by
  ext i j
  rw [adjH_apply]
  unfold middlePart
  by_cases h : Mid k r i ∧ Mid k r j
  · rw [if_pos ⟨(mid_tau j).2 h.2, (mid_tau i).2 h.1⟩, if_pos h, adjH_apply]
  · rw [if_neg (fun h' => h ⟨(mid_tau i).1 h'.2, (mid_tau j).1 h'.1⟩), if_neg h, star_zero, mul_zero, zero_mul]

theorem adjH_w0conj (M : Mat k r) : adjH (w0B k r * M * w0B k r) = w0B k r * adjH M * w0B k r := by
  rw [adjH_mul, adjH_mul, adjoint_long_weyl_element, Matrix.mul_assoc]

theorem tD_apply (x : Fin r → ℂ) (i j : Fin (2 * r + k + 1)) :
    tD k r x i j = if i = j then dv k r x i else 0 := by
  unfold tD; rw [Matrix.diagonal_apply]

theorem dv_tau (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : star (dv k r x (tau k r i)) = -dv k r x i := by
  have hi := i.isLt
  unfold dv
  by_cases h1 : i.val < r
  · have hv : (tau k r i).val = 2 * r + k - i.val := by rw [tau_val, if_pos (Or.inl h1)]
    have ht : ¬ (tau k r i).val < r := by omega
    have ht2 : ¬ (tau k r i).val ≤ r + k := by omega
    rw [dif_neg ht, dif_neg ht2, dif_pos h1, star_neg, star_star]
    congr 2; apply Fin.ext; simp only; omega
  · by_cases h2 : i.val ≤ r + k
    · have hv : (tau k r i).val = i.val := by rw [tau_val, if_neg (by omega)]
      have ht : ¬ (tau k r i).val < r := by omega
      have ht2 : (tau k r i).val ≤ r + k := by omega
      rw [dif_neg ht, dif_pos ht2, dif_neg h1, dif_pos h2, star_zero, neg_zero]
    · have hv : (tau k r i).val = 2 * r + k - i.val := by rw [tau_val, if_pos (Or.inr (by omega))]
      have ht : (tau k r i).val < r := by omega
      rw [dif_pos ht, dif_neg h1, dif_neg h2, neg_neg]
      congr 2; apply Fin.ext; simp only; omega

theorem adjH_tD (x : Fin r → ℂ) : adjH (tD k r x) = -tD k r x := by
  ext i j
  rw [adjH_apply, Matrix.neg_apply, tD_apply, tD_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, dv_tau]
    calc sgn k r i * -dv k r x i * sgn k r i = -(sgn k r i * sgn k r i) * dv k r x i := by ring
      _ = -dv k r x i := by rw [sgn_mul_self]; ring
  · rw [if_neg (fun h' => h (by rw [← tau_tau i, ← tau_tau j, h'])), if_neg h, star_zero, mul_zero, zero_mul, neg_zero]

theorem lm_mem {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) : Lm k r v ∈ uH k r := by
  obtain ⟨h1, -, h3, h4⟩ : v.1 ∈ lieNS k r ∧ v.2.1 ∈ (⊤ : Submodule ℝ (Fin r → ℂ)) ∧ v.2.2.1 ∈ uWb k r ∧
      v.2.2.2 ∈ lieNS k r := by
    simp only [Vs, Submodule.mem_prod] at hv; exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
  show adjH (w0B k r * v.1 * w0B k r + tD k r v.2.1 + v.2.2.1 - v.2.2.2) +
    (w0B k r * v.1 * w0B k r + tD k r v.2.1 + v.2.2.1 - v.2.2.2) = 0
  have a1 : adjH v.1 = -v.1 := eq_neg_of_add_eq_zero_left h1.2
  have a3 : adjH v.2.2.1 = -v.2.2.1 := eq_neg_of_add_eq_zero_left h3.1
  have a4 : adjH v.2.2.2 = -v.2.2.2 := eq_neg_of_add_eq_zero_left h4.2
  rw [adjH_sub, adjH_add, adjH_add, adjH_w0conj, a1, adjH_tD, a3, a4, Matrix.mul_neg, Matrix.neg_mul]
  abel

end Formalism.L2.SG.Pf.BH.Sw

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem posP_neg (Y : Mat k r) : posP (-Y) = -posP Y := by
  ext i j; simp only [posP, Matrix.neg_apply]; split_ifs <;> simp
theorem negP_neg (Y : Mat k r) : negP (-Y) = -negP Y := by
  ext i j; simp only [negP, Matrix.neg_apply]; split_ifs <;> simp
theorem middlePart_neg (Y : Mat k r) : middlePart (-Y) = -middlePart Y := by
  ext i j; simp only [middlePart, Matrix.neg_apply]; split_ifs <;> simp

theorem long_weyl_conj_conj (M : Mat k r) : w0B k r * (w0B k r * M * w0B k r) * w0B k r = M := by
  simp only [← Matrix.mul_assoc]
  rw [w0Sq k r, Matrix.one_mul, Matrix.mul_assoc, w0Sq k r, Matrix.mul_one]

theorem eI_val' (a : Fin r) : (eI k r a).val = a.val := rfl

theorem diag_star {Y : Mat k r} (hadj : adjH Y = -Y) (i : Fin (2 * r + k + 1)) :
    Y i i = -star (Y (tau k r i) (tau k r i)) := by
  have h := congrFun (congrFun hadj i) i
  rw [adjH_apply, Matrix.neg_apply] at h
  have hs : sgn k r i * star (Y (tau k r i) (tau k r i)) * sgn k r i = star (Y (tau k r i) (tau k r i)) := by
    calc sgn k r i * star (Y (tau k r i) (tau k r i)) * sgn k r i
        = (sgn k r i * sgn k r i) * star (Y (tau k r i) (tau k r i)) := by ring
      _ = star (Y (tau k r i) (tau k r i)) := by rw [sgn_mul_self, one_mul]
  rw [hs] at h
  rw [h, neg_neg]

theorem decomp {Y : Mat k r} (hadj : adjH Y = -Y) : negP Y + tD k r (xOf Y) + middlePart Y + posP Y = Y := by
  ext i j
  simp only [Matrix.add_apply, tD_apply]
  unfold negP middlePart posP
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_trichotomy (dg k r i) (dg k r j) with h | h | h
  · have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
    have hm : ¬ (Mid k r i ∧ Mid k r j) := fun hm => by
      rw [mid_iff, mid_iff] at hm; omega
    rw [if_neg (by omega), if_neg hne, if_neg hm, if_pos h]; ring
  · by_cases hm : Mid k r i
    · have hmj : Mid k r j := by rw [mid_iff] at hm ⊢; omega
      by_cases hij : i = j
      · subst hij
        have h0 : dv k r (xOf Y) i = 0 := by
          have hm2 : r ≤ i.val ∧ i.val ≤ r + k := hm
          unfold dv
          rw [dif_neg (by omega), dif_pos hm2.2]
        rw [if_neg (lt_irrefl _), if_pos rfl, if_pos ⟨hm, hm⟩, h0]; ring
      · rw [if_neg (by omega), if_neg hij, if_pos ⟨hm, hmj⟩, if_neg (by omega)]; ring
    · have hij : i = j := dg_inj h hm
      subst hij
      have hmm : ¬ (Mid k r i ∧ Mid k r i) := fun h' => hm h'.1
      rw [if_neg (lt_irrefl _), if_pos rfl, if_neg hmm]
      have hm' : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := hm
      unfold dv xOf
      by_cases h1 : i.val < r
      · rw [dif_pos h1]
        have : eI k r ⟨i.val, h1⟩ = i := Fin.ext rfl
        rw [this]; ring
      · have h2 : ¬ i.val ≤ r + k := fun h2 => hm' ⟨by omega, h2⟩
        rw [dif_neg h1, dif_neg h2]
        have e : eI k r ⟨2 * r + k - i.val, by omega⟩ = tau k r i := by
          apply Fin.ext; rw [eI_val', tau_val, if_pos (Or.inr (by omega))]
        rw [e, ← diag_star hadj]; ring
  · have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
    have hm : ¬ (Mid k r i ∧ Mid k r j) := fun hm => by
      rw [mid_iff, mid_iff] at hm; omega
    rw [if_pos h, if_neg hne, if_neg hm, if_neg (by omega)]; ring

theorem lm_surj {Y : Mat k r} (hY : Y ∈ uH k r) : ∃ v ∈ Vs k r, Lm k r v = Y := by
  have hadj : adjH Y = -Y := eq_neg_of_add_eq_zero_left hY
  refine ⟨(w0B k r * negP Y * w0B k r, xOf Y, middlePart Y, -posP Y), ?_, ?_⟩
  · have m1 : w0B k r * negP Y * w0B k r ∈ lieNS k r := by
      show w0B k r * negP Y * w0B k r ∈ lieN k r
      refine ⟨?_, ?_⟩
      · intro i j hij
        rw [longestWeylElementGL_conj_apply_rev]
        unfold negP
        rw [if_neg]
        rw [dg_tau, dg_tau]
        have := dg_le (k := k) (r := r) i; have := dg_le (k := k) (r := r) j
        omega
      · rw [adjH_w0conj, adjH_negP, hadj, negP_neg, Matrix.mul_neg, Matrix.neg_mul, neg_add_cancel]
    have m3 : middlePart Y ∈ uWb k r := by
      refine ⟨?_, ?_⟩
      · show adjH (middlePart Y) + middlePart Y = 0
        rw [adjH_midP, hadj, middlePart_neg, neg_add_cancel]
      · intro i j h
        unfold middlePart; rw [if_neg h]
    have m4 : -posP Y ∈ lieNS k r := by
      show -posP Y ∈ lieN k r
      refine ⟨?_, ?_⟩
      · intro i j hij
        rw [Matrix.neg_apply]
        unfold posP
        rw [if_neg (by omega), neg_zero]
      · rw [adjH_neg, adjH_posP, hadj, posP_neg, neg_neg, add_neg_cancel]
    exact Submodule.mem_prod.2 ⟨m1, Submodule.mem_prod.2 ⟨Submodule.mem_top, Submodule.mem_prod.2 ⟨m3, m4⟩⟩⟩
  · show w0B k r * (w0B k r * negP Y * w0B k r) * w0B k r + tD k r (xOf Y) + middlePart Y - -posP Y = Y
    rw [long_weyl_conj_conj, sub_neg_eq_add]
    exact decomp hadj

end Formalism.L2.SG.Pf.BH.Sw

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem RL_sq (M : Mat k r) : ‖RL M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [RL, Formalism.MainNotions.S.realifyFun, WithLp.equiv]
  ring

theorem dv_sq_sum (x : Fin r → ℂ) : ∑ i, ‖dv k r x i‖ ^ 2 = 2 * ∑ a, ‖x a‖ ^ 2 := by
  let e : Fin r → Fin (2 * r + k + 1) := fun a => ⟨a.val, by omega⟩
  let f : Fin r → Fin (2 * r + k + 1) := fun a => ⟨2 * r + k - a.val, by omega⟩
  have he : Function.Injective e := fun a b h => Fin.ext (by simpa [e] using congrArg Fin.val h)
  have hf : Function.Injective f := fun a b h => by
    have := congrArg Fin.val h; simp [f] at this; exact Fin.ext (by omega)
  have hdisj : Disjoint (Finset.univ.image e) (Finset.univ.image f) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi hi'
    obtain ⟨a, rfl⟩ := hi; obtain ⟨b, hb⟩ := hi'
    have := congrArg Fin.val hb; simp [e, f] at this; omega
  have hsupp : ∀ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))),
      i ∉ Finset.univ.image e ∪ Finset.univ.image f → ‖dv k r x i‖ ^ 2 = 0 := by
    intro i _ hi
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists] at hi
    have h1 : ¬ i.val < r := fun h => hi.1 ⟨i.val, h⟩ (Fin.ext rfl)
    have h2 : i.val ≤ r + k := by
      by_contra h
      exact hi.2 ⟨2 * r + k - i.val, by have := i.isLt; omega⟩ (Fin.ext (by simp [f]; have := i.isLt; omega))
    unfold dv; rw [dif_neg h1, dif_pos h2]; simp
  rw [← Finset.sum_subset (Finset.subset_univ _) hsupp, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => he h),
    Finset.sum_image (fun a _ b _ h => hf h), two_mul]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    unfold dv; rw [dif_pos (show (e a).val < r from a.isLt)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : ¬ (f a).val < r := by simp [f]; omega
    have h2 : ¬ (f a).val ≤ r + k := by simp [f]; have := a.isLt; omega
    unfold dv; rw [dif_neg h1, dif_neg h2, norm_neg, norm_star]
    congr 2; congr 1; apply Fin.ext; simp [f]; omega

theorem tD_sq_sum (x : Fin r → ℂ) : ∑ i, ∑ j, ‖tD k r x i j‖ ^ 2 = 2 * ∑ a, ‖x a‖ ^ 2 := by
  rw [← dv_sq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [tD_apply]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hj; rw [if_neg (Ne.symm hj), norm_zero]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

theorem conj_sq_sum (X : Mat k r) : ∑ i, ∑ j, ‖(w0B k r * X * w0B k r) i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  simp only [longestWeylElementGL_conj_apply_rev]
  let σ : Equiv.Perm (Fin (2 * r + k + 1)) := Function.Involutive.toPerm (tau k r) tau_tau
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ‖X (tau k r (tau k r i)) (tau k r (tau k r j))‖ ^ 2 = ‖X i j‖ ^ 2
  rw [tau_tau, tau_tau]

theorem lm_norm {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) :
    ‖RL (Lm k r v)‖ ^ 2 = ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2 := by
  obtain ⟨h1, -, h3, h4⟩ : v.1 ∈ lieNS k r ∧ v.2.1 ∈ (⊤ : Submodule ℝ (Fin r → ℂ)) ∧ v.2.2.1 ∈ uWb k r ∧
      v.2.2.2 ∈ lieNS k r := by
    simp only [Vs, Submodule.mem_prod] at hv; exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
  have f1 : Fil 1 v.1 := h1.1
  have f4 : Fil 1 v.2.2.2 := h4.1
  have hpt : ∀ i j, ‖(Lm k r v) i j‖ ^ 2 = ‖(w0B k r * v.1 * w0B k r) i j‖ ^ 2 + ‖tD k r v.2.1 i j‖ ^ 2 +
      ‖v.2.2.1 i j‖ ^ 2 + ‖v.2.2.2 i j‖ ^ 2 := by
    intro i j
    show ‖(w0B k r * v.1 * w0B k r + tD k r v.2.1 + v.2.2.1 - v.2.2.2) i j‖ ^ 2 = _
    simp only [Matrix.sub_apply, Matrix.add_apply, longestWeylElementGL_conj_apply_rev, tD_apply]
    have hi := dg_le (k := k) (r := r) i
    have hj := dg_le (k := k) (r := r) j
    rcases lt_trichotomy (dg k r i) (dg k r j) with h | h | h
    · have a0 : v.1 (tau k r i) (tau k r j) = 0 := f1 _ _ (by rw [dg_tau, dg_tau]; omega)
      have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
      have c0 : v.2.2.1 i j = 0 := h3.2 i j (fun hm => by rw [mid_iff, mid_iff] at hm; omega)
      rw [a0, if_neg hne, c0]; simp
    · have a0 : v.1 (tau k r i) (tau k r j) = 0 := f1 _ _ (by rw [dg_tau, dg_tau]; omega)
      have d0 : v.2.2.2 i j = 0 := f4 _ _ (by omega)
      rw [a0, d0]
      by_cases hm : Mid k r i
      · by_cases hij : i = j
        · subst hij
          have h0 : dv k r v.2.1 i = 0 := by
            have hm2 : r ≤ i.val ∧ i.val ≤ r + k := hm
            unfold dv; rw [dif_neg (by omega), dif_pos hm2.2]
          rw [if_pos rfl, h0]; simp
        · rw [if_neg hij]; simp
      · have hij : i = j := dg_inj h hm
        subst hij
        have c0 : v.2.2.1 i i = 0 := h3.2 i i (fun h' => hm h'.1)
        rw [c0]; simp
    · have d0 : v.2.2.2 i j = 0 := f4 _ _ (by omega)
      have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
      have c0 : v.2.2.1 i j = 0 := h3.2 i j (fun hm => by rw [mid_iff, mid_iff] at hm; omega)
      rw [d0, if_neg hne, c0]; simp
  rw [RL_sq, RL_sq, RL_sq, RL_sq]
  simp_rw [hpt]
  simp only [Finset.sum_add_distrib]
  rw [conj_sq_sum, tD_sq_sum]

theorem lIso : LIso := fun k r => ⟨fun v hv => lm_mem hv, fun Y hY => lm_surj hY, fun v hv => lm_norm hv⟩

end Formalism.L2.SG.Pf.BH.Sw
