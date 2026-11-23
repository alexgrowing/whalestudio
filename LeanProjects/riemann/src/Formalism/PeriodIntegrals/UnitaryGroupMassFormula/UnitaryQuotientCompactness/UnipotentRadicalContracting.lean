import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MulVecBvecApply

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

lemma uw_conj_N {h n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : h * n * h⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hn ⊢
  obtain ⟨hnU, hnc⟩ := hn
  have hU : h ∈ UH (Hpk k r) := hh.1
  have hhi := inv_mem_UW hh
  refine ⟨mul_mem_UH (mul_mem_UH hU hnU) (inv_mem_UH hU), fun i j hj hi => ?_⟩
  by_cases hjW : r ≤ j.val
  · have hir : r ≤ i.val := by
      have := min_eq_right hjW
      omega
    have hA : ∀ b, inW k r b → (h * n) i b = h i b := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · rw [hnc b b hb2 (by rw [min_eq_right hb1]; exact hb1), if_pos rfl, mul_one]
      · intro a _ hab
        by_cases har : r ≤ a.val
        · rw [hnc a b hb2 (by rw [min_eq_right hb1]; exact har), if_neg hab, mul_zero]
        · rw [uw_block hh i a (fun h' => har h'.2.1),
            if_neg (fun e => har (by rw [← e]; exact hir)), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ b) h'
    have hone : (h * h⁻¹) i j = if i = j then 1 else 0 := by
      rw [mul_inv_UH hU, Matrix.one_apply]
    rw [← hone, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : inW k r b
    · rw [hA b hb]
    · rw [uw_block hhi b j (fun h' => hb h'.1),
        if_neg (fun e => hb (by rw [e]; exact ⟨hjW, hj⟩)), mul_zero, mul_zero]
  · push Not at hjW
    have hmin : min j.val r = j.val := min_eq_left hjW.le
    have hij : j.val ≤ i.val := by omega
    have hjn : ¬ inW k r j := fun h' => absurd h'.1 (by omega)
    have hcol : (h * n * h⁻¹) i j = (h * n) i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [uw_col_out hhi j hjn j, if_pos rfl, mul_one]
      · intro b _ hb
        rw [uw_col_out hhi j hjn b, if_neg hb, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ j) h'
    rw [hcol, Matrix.mul_apply]
    by_cases hiW : inW k r i
    · have hi1 := hiW.1
      rw [if_neg (fun e => by rw [e] at hi1; omega)]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases haW : inW k r a
      · have ha1 := haW.1
        rw [hnc a j (by omega) (by rw [hmin]; omega), if_neg (fun e => by rw [e] at ha1; omega),
          mul_zero]
      · rw [uw_block hh i a (fun h' => haW h'.2), if_neg (fun e => haW (by rw [← e]; exact hiW)),
          zero_mul]
    · rw [Finset.sum_eq_single i]
      · rw [uw_block hh i i (fun h' => hiW h'.1), if_pos rfl, one_mul,
          hnc i j (by omega) (by rw [hmin]; exact hij)]
      · intro a _ hai
        rw [uw_block hh i a (fun h' => hiW h'.1), if_neg (Ne.symm hai), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ i) h'

def fexp (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else (r : ℤ) + k - i.val

lemma fexp_piI (i : Fin (2 * r + k + 1)) : fexp k r (piI k r i) = - fexp k r i := by
  have hi := i.isLt
  have hv := piI_val (k := k) (r := r) i
  simp only [fexp]
  split_ifs at hv ⊢ <;> omega

lemma fexp_inW {i : Fin (2 * r + k + 1)} (hi : inW k r i) : fexp k r i = 0 := by
  obtain ⟨h1, h2⟩ := hi
  simp only [fexp]
  split_ifs <;> omega

lemma fexp_gap {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hW : ¬ (inW k r i ∧ inW k r j)) :
    1 ≤ fexp k r i - fexp k r j := by
  simp only [inW] at hW
  simp only [fexp]
  split_ifs <;> omega

def dS (k r : ℕ) (s : ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  diagonal fun i => ((s : ℂ)) ^ (fexp k r i)

lemma dS_mul_dS_inv {s : ℝ} (hs : s ≠ 0) : dS k r s * dS k r s⁻¹ = 1 := by
  rw [dS, dS, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← mul_zpow, Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs), _root_.one_zpow]

lemma dS_conj_apply (s : ℝ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (dS k r s * g * dS k r s⁻¹) i j = (s : ℂ) ^ (fexp k r i) * g i j * ((s⁻¹ : ℝ) : ℂ) ^ (fexp k r j) := by
  rw [dS, dS, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma dS_mem_UH {s : ℝ} (hs : s ≠ 0) : dS k r s ∈ UH (Hpk k r) := by
  show (dS k r s)ᴴ * Hpk k r * dS k r s = Hpk k r
  ext i j
  rw [dS, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Hpk_apply]
  split_ifs with h
  · subst h
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    rw [fexp_piI, Pi.star_apply, star_zpow₀, Complex.star_def, Complex.conj_ofReal, _root_.zpow_neg]
    field_simp
  · simp

lemma dS_conj_fix {s : ℝ} (hs : s ≠ 0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (i j : Fin (2 * r + k + 1)) (hg : g i j = if i = j then 1 else 0) :
    (dS k r s * g * dS k r s⁻¹) i j = if i = j then 1 else 0 := by
  rw [dS_conj_apply, hg]
  split_ifs with h
  · subst h
    rw [mul_one, ← mul_zpow, Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs),
      _root_.one_zpow]
  · simp

lemma dS_conj_UW {s : ℝ} (hs : s ≠ 0) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : dS k r s * h * dS k r s⁻¹ = h := by
  ext i j
  by_cases hij : inW k r i ∧ inW k r j
  · rw [dS_conj_apply, fexp_inW hij.1, fexp_inW hij.2, zpow_zero, zpow_zero, one_mul, mul_one]
  · rw [dS_conj_fix hs i j (uw_block hh i j hij), uw_block hh i j hij]

lemma dS_conj_N {s : ℝ} (hs : s ≠ 0) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : dS k r s * n * dS k r s⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hn ⊢
  exact ⟨mul_mem_UH (mul_mem_UH (dS_mem_UH hs) hn.1) (dS_mem_UH (inv_ne_zero hs)),
    fun i j hj hi => dS_conj_fix hs i j (hn.2 i j hj hi)⟩

lemma dS_conj_S {s : ℝ} (hs : s ≠ 0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Sset k r z) : dS k r s * g * dS k r s⁻¹ ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  have h1 : dS k r s⁻¹ * dS k r s = 1 := by
    have := dS_mul_dS_inv (k := k) (r := r) (inv_ne_zero hs)
    rwa [inv_inv] at this
  have e : dS k r s * (h * m) * dS k r s⁻¹ =
      (dS k r s * h * dS k r s⁻¹) * (dS k r s * m * dS k r s⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (dS k r s⁻¹) (dS k r s), h1, Matrix.one_mul]
  exact ⟨h, hh, _, dS_conj_N hs hm, by rw [e, dS_conj_UW hs hh]⟩

lemma dS_inv_eq {s : ℝ} (hs : s ≠ 0) : (dS k r s)⁻¹ = dS k r s⁻¹ :=
  Matrix.inv_eq_right_inv (dS_mul_dS_inv hs)

lemma dS_conj_S_iff {s : ℝ} (hs : s ≠ 0) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    dS k r s * g * (dS k r s)⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z := by
  rw [dS_inv_eq hs]
  have h1 : dS k r s⁻¹ * dS k r s = 1 := by
    have := dS_mul_dS_inv (k := k) (r := r) (inv_ne_zero hs)
    rwa [inv_inv] at this
  constructor
  · intro hg
    have h2 := dS_conj_S (inv_ne_zero hs) hg
    rw [inv_inv] at h2
    have e : dS k r s⁻¹ * (dS k r s * g * dS k r s⁻¹) * dS k r s = g := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    rwa [e] at h2
  · exact dS_conj_S hs

lemma norm_dS_conj_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) (i j) :
    ‖(dS k r s * n * (dS k r s)⁻¹ - 1) i j‖ ≤ s * ‖n i j‖ := by
  have hs := hs0.ne'
  rw [dS_inv_eq hs, Matrix.sub_apply]
  by_cases hfix : n i j = if i = j then 1 else 0
  · rw [dS_conj_fix hs i j hfix, Matrix.one_apply, sub_self, norm_zero]
    positivity
  · have hlt : i.val < j.val := by
      by_contra hle
      exact hfix (n_ut hn i j (by omega))
    have hne : i ≠ j := fun e => by rw [e] at hlt; omega
    have hW : ¬ (inW k r i ∧ inW k r j) := by
      rintro ⟨⟨hi1, -⟩, -, hj2⟩
      exact hfix (((mem_Nset_iff n).mp hn).2 i j hj2 (by omega))
    have hd := fexp_gap hlt hW
    rw [dS_conj_apply, Matrix.one_apply_ne hne, sub_zero, norm_mul, norm_mul, norm_zpow, norm_zpow,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs0.le,
      Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
    have key : s ^ fexp k r i * s⁻¹ ^ fexp k r j = s ^ (fexp k r i - fexp k r j) := by
      rw [_root_.inv_zpow, ← _root_.zpow_neg, ← zpow_add₀ hs, sub_eq_add_neg]
    have hle : s ^ (fexp k r i - fexp k r j) ≤ s := by
      calc s ^ (fexp k r i - fexp k r j) ≤ s ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hs0 hs1 hd
        _ = s := zpow_one s
    calc s ^ fexp k r i * ‖n i j‖ * s⁻¹ ^ fexp k r j = s ^ (fexp k r i - fexp k r j) * ‖n i j‖ := by
          rw [← key]; ring
      _ ≤ s * ‖n i j‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)

theorem unipotent_radical_contracting : NContract := by
  intro k r z _ n hn ε hε
  have hM : 0 ≤ ∑ i, ∑ j, ‖n i j‖ := by positivity
  have hs0 : 0 < min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) := lt_min one_pos (div_pos hε (by linarith))
  have hs1 : min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) ≤ 1 := min_le_left _ _
  refine ⟨dS k r (min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1))),
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (dS_mul_dS_inv hs0.ne')),
    fun g => dS_conj_S_iff hs0.ne' g, fun i j => ?_⟩
  have hentry : ‖n i j‖ ≤ ∑ i, ∑ j, ‖n i j‖ :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (n i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖n i j‖)
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
  calc ‖(dS k r _ * n * (dS k r _)⁻¹ - 1) i j‖ ≤ _ * ‖n i j‖ := norm_dS_conj_le hs0 hs1 hn i j
    _ ≤ (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) * ∑ i, ∑ j, ‖n i j‖ :=
        mul_le_mul (min_le_right _ _) hentry (norm_nonneg _) (div_pos hε (by linarith)).le
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

end PI.QuotSetU.UnitaryGroupMassFormula.SW
