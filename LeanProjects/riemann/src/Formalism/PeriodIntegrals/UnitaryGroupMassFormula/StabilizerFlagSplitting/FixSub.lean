import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.SubFlag
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic

noncomputable section

namespace PI.StabSplit.FixW

def uOf (k r : ℕ) (g : B.Mat k r) : B.Mat k r :=
  Matrix.of fun i j =>
    if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then g i j
    else if i = j then 1 else 0

lemma uOf_out_col {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hj : j.val < r ∨ r + k < j.val) : uOf k r g i j = if i = j then 1 else 0 := by
  simp only [uOf, of_apply]
  rw [if_neg (by omega)]

lemma uOf_out_row {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi : i.val < r ∨ r + k < i.val) : uOf k r g i j = if i = j then 1 else 0 := by
  simp only [uOf, of_apply]
  rw [if_neg (by omega)]

lemma uOf_in {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi1 : r ≤ i.val) (hi2 : i.val ≤ r + k) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    uOf k r g i j = g i j := by
  simp only [uOf, of_apply]
  rw [if_pos ⟨⟨hi1, hi2⟩, hj1, hj2⟩]

lemma uOf_W_out {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi1 : r ≤ i.val) (hi2 : i.val ≤ r + k) (hj : j.val < r ∨ r + k < j.val) :
    uOf k r g i j = 0 := by
  rw [uOf_out_col g i j hj, if_neg]
  intro h; subst h; omega

lemma herm_entry {k r : ℕ} (A C : B.Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * C) i j = ∑ p, star (A p i) * sgn k r p * C (sig k r p) j := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, conjTranspose_apply, Hpk_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [mul_ite, ite_mul, Finset.sum_ite_eq']

lemma mulVec_bvec {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    A *ᵥ bvec j = fun i => A i j := by
  ext i; simp [bvec, mulVec, dotProduct, Pi.single_apply]

lemma fix_col {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (j : Fin (2 * r + k + 1)) (hj : j.val < r) (i : Fin (2 * r + k + 1)) :
    g i j = if i = j then 1 else 0 := by
  have h := congrFun (hg.2 ⟨j.val, by omega⟩) i
  have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
  simp only [fvec, dif_pos hj, e, mulVec_bvec] at h
  rw [h]; simp [bvec, Pi.single_apply]

lemma isometry_fix_flagAnisotropicVector_of_fix_frame {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z) :
    g *ᵥ z = z := by
  have h := hg.2 (Fin.last r)
  simpa [fvec] using h

lemma fix_zero {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (i j : Fin (2 * r + k + 1)) (hi : r + k < i.val) (hj2 : j.val ≤ r + k) : g i j = 0 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  set a := sig k r i with ha
  have har : a.val < r := by rw [ha, sig_hi k r i hi]; have := i.isLt; omega
  have e := congrFun (congrFun hU a) j
  rw [herm_entry, Finset.sum_eq_single a] at e
  · rw [fix_col hg a har a, if_pos rfl, ha, sig_sig] at e
    have hs : sgn k r (sig k r i) = 1 := by
      unfold sgn; rw [if_neg]; rw [sig_hi k r i hi]; have := i.isLt; omega
    rw [hs, star_one, one_mul, one_mul, Hpk_eq, if_neg] at e
    · exact e
    · rw [← ha, sig_sig]; intro h; subst h; omega
  · intro p _ hp
    rw [fix_col hg a har p, if_neg hp, star_zero, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma uOf_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z) :
    uOf k r g ∈ UH (Hpk k r) := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  show (uOf k r g)ᴴ * Hpk k r * uOf k r g = Hpk k r
  ext i j
  rw [herm_entry]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [← congrFun (congrFun hU i) j, herm_entry]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [sig_mid k r p hp.1 hp.2, uOf_in g p i hp.1 hp.2 hi.1 hi.2, uOf_in g p j hp.1 hp.2 hj.1 hj.2]
      · rw [uOf_out_row g p i (by omega), if_neg (by intro h; subst h; omega), star_zero, zero_mul,
          zero_mul]
        rcases (show p.val < r ∨ r + k < p.val by omega) with hp' | hp'
        · rw [fix_zero hg (sig k r p) j (by rw [sig_lo k r p hp']; omega) hj.2, mul_zero]
        · rw [fix_zero hg p i hp' hi.2, star_zero, zero_mul, zero_mul]
    · rw [Finset.sum_eq_single (sig k r j)]
      · rw [sig_sig, uOf_out_col g j j (by omega), if_pos rfl, mul_one]
        have hsj : (sig k r j).val < r ∨ r + k < (sig k r j).val := by
          have := j.isLt; rw [sig_val]; split_ifs <;> omega
        rw [uOf_out_row g (sig k r j) i hsj, if_neg (by intro h; rw [← h] at hi; omega), star_zero,
          zero_mul, Hpk_eq, if_neg]
        rw [sig_mid k r i hi.1 hi.2]; intro h; subst h; omega
      · intro p _ hp
        rw [uOf_out_col g _ j (by omega), if_neg (by intro h; apply hp; rw [← h, sig_sig]), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single i]
    · rw [uOf_out_col g i i (by omega), if_pos rfl, star_one, one_mul]
      have hsi : (sig k r i).val < r ∨ r + k < (sig k r i).val := by
        have := i.isLt; rw [sig_val]; split_ifs <;> omega
      rw [uOf_out_row g (sig k r i) j hsi, Hpk_eq]
      by_cases h : sig k r i = j
      · rw [if_pos h, if_pos h.symm, mul_one]
      · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
    · intro p _ hp
      rw [uOf_out_col g p i (by omega), if_neg hp, star_zero, zero_mul, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma uOf_fix_out {k r : ℕ} (g : B.Mat k r) (c : Fin (2 * r + k + 1))
    (hc : c.val < r ∨ r + k < c.val) : uOf k r g *ᵥ bvec c = bvec c := by
  rw [mulVec_bvec]; ext i
  rw [uOf_out_col g i c hc]; simp [bvec, Pi.single_apply]

lemma unipotent_part_fixes_vector {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : B.Mat k r}
    (hg : g ∈ FixSet k r z) : uOf k r g *ᵥ z = z := by
  ext i
  have hgz := congrFun (isometry_fix_flagAnisotropicVector_of_fix_frame hg) i
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · rw [← hgz]
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
    · rw [uOf_in g i l hi.1 hi.2 hl.1 hl.2]
    · rw [hz l (by omega), mul_zero, mul_zero]
  · simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · rw [uOf_out_row g i i (by omega), if_pos rfl, one_mul]
    · intro l _ hl
      rw [uOf_out_row g i l (by omega), if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma uOf_UW {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : B.Mat k r}
    (hg : g ∈ FixSet k r z) : uOf k r g ∈ UWset k r z := by
  refine ⟨uOf_mem hg, fun a => ⟨?_, ?_⟩, unipotent_part_fixes_vector hz hg⟩
  · exact uOf_fix_out g _ (Or.inl (by simp [eI]))
  · exact uOf_fix_out g _ (Or.inr (by simp [esI]; omega))

def yv (k r : ℕ) (g : B.Mat k r) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if i.val < r then g i j else if i = j then 1 else 0

lemma uOf_yv {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (j : Fin (2 * r + k + 1)) (hj : j.val ≤ r + k) : uOf k r g *ᵥ yv k r g j = fun i => g i j := by
  ext i
  simp only [mulVec, dotProduct]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · have key : ∀ l, uOf k r g i l * yv k r g j l =
        if l = j then (if r ≤ j.val then g i j else 0) else 0 := by
      intro l
      by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
      · rw [uOf_in g i l hi.1 hi.2 hl.1 hl.2]
        simp only [yv, if_neg (show ¬ l.val < r by omega)]
        by_cases hlj : l = j
        · subst hlj; rw [if_pos rfl, if_pos rfl, if_pos hl.1, mul_one]
        · rw [if_neg hlj, if_neg hlj, mul_zero]
      · rw [uOf_W_out g i l hi.1 hi.2 (by omega), zero_mul]
        by_cases hlj : l = j
        · subst hlj; rw [if_pos rfl, if_neg (by omega)]
        · rw [if_neg hlj]
    rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _)]
    by_cases hjr : r ≤ j.val
    · rw [if_pos hjr]
    · rw [if_neg hjr, fix_col hg j (by omega) i, if_neg]; intro h; subst h; omega
  · rw [Finset.sum_eq_single i]
    · rw [uOf_out_row g i i (by omega), if_pos rfl, one_mul]
      simp only [yv]
      by_cases hir : i.val < r
      · rw [if_pos hir]
      · rw [if_neg hir, if_neg (by intro h; subst h; omega)]
        by_cases hjr : j.val < r
        · rw [fix_col hg j hjr i, if_neg (by intro h; subst h; omega)]
        · rw [fix_zero hg i j (by omega) hj]
    · intro l _ hl
      rw [uOf_out_row g i l (by omega), if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem fixed_point_subgroup : FixSub := by
  intro k r z hz g hg
  have hu := uOf_UW hz hg
  have hH : (Hpk k r).det ≠ 0 := by
    have h2 := congrArg Matrix.det (Hpk_sq k r)
    rw [det_mul, det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have hdet : IsUnit (uOf k r g).det := by
    have h := congrArg Matrix.det hu.1
    rw [det_mul, det_mul, det_conjTranspose] at h
    refine isUnit_iff_ne_zero.mpr (fun h0 => hH ?_)
    rw [← h, h0, mul_zero]
  refine ⟨uOf k r g, hu, (uOf k r g)⁻¹ * g, ?_, ?_⟩
  · have hm : (uOf k r g)⁻¹ * g ∈ UH (Hpk k r) := by
      have hinv := (uHGroup (2 * r + k + 1) (Hpk k r) (isUnit_iff_ne_zero.mpr hH)).2
      exact hinv.1 _ (hinv.2 _ hu.1).2 _ hg.1
    refine ⟨hm, fun a i hi => ?_, fun i j h1 h2 h3 => ?_⟩
    · have e : (eI k r a).val < r := by simp [eI]
      have hy := congrFun (uOf_yv hg (eI k r a) (by omega)) i
      have hc : ((uOf k r g)⁻¹ * g) i (eI k r a) = yv k r g (eI k r a) i := by
        rw [← congrFun (mulVec_bvec ((uOf k r g)⁻¹ * g) (eI k r a)) i, ← mulVec_mulVec,
          mulVec_bvec g, ← uOf_yv hg (eI k r a) (by omega), mulVec_mulVec,
          nonsing_inv_mul _ hdet, one_mulVec]
      rw [hc]; simp only [yv]
      by_cases hir : i.val < r
      · rw [if_pos hir, fix_col hg _ e i]
      · rw [if_neg hir]
    · have hc : ((uOf k r g)⁻¹ * g) i j = yv k r g j i := by
        rw [← congrFun (mulVec_bvec ((uOf k r g)⁻¹ * g) j) i, ← mulVec_mulVec,
          mulVec_bvec g, ← uOf_yv hg j h2, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
      rw [hc]; simp only [yv, if_neg (show ¬ i.val < r by omega)]
  · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul]

end PI.StabSplit.FixW

namespace PI.StabSplit

theorem fixed_point_subgroup : FixSub := FixW.fixed_point_subgroup

end PI.StabSplit
