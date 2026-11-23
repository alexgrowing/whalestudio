import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.SGroup

open Matrix

namespace CompanionTheory.D.Upq.QuotSetU

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ}

local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def expo (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else -((i.val : ℤ) - r - k)

theorem expo_add_piI (i : Fin (2 * r + k + 1)) : expo k r i + expo k r (piI k r i) = 0 := by
  have hp := piI_val (k := k) (r := r) i
  have := i.isLt
  unfold expo
  split_ifs at hp ⊢ <;> omega

theorem expo_eq_zero_of_inW {i : Fin (2 * r + k + 1)} (hi : inW k r i) : expo k r i = 0 := by
  unfold expo; unfold inW at hi; split_ifs <;> omega

theorem expo_lt {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hW : ¬ (inW k r i ∧ inW k r j)) :
    expo k r j + 1 ≤ expo k r i := by
  unfold expo; unfold inW at hW; split_ifs <;> omega

noncomputable def dvec (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ := ((t ^ expo k r i : ℝ) : ℂ)

noncomputable def cdiag (k r : ℕ) (t : ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  diagonal (dvec (k := k) (r := r) t)

theorem dvec_mul_inv {t : ℝ} (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) :
    dvec (k := k) (r := r) t i * dvec t⁻¹ i = 1 := by
  rw [dvec, dvec, ← Complex.ofReal_mul, ← mul_zpow, mul_inv_cancel₀ ht, _root_.one_zpow,
    Complex.ofReal_one]

theorem dvec_of_inW {t : ℝ} {i : Fin (2 * r + k + 1)} (hi : inW k r i) : dvec (k := k) (r := r) t i = 1 := by
  rw [dvec, expo_eq_zero_of_inW hi, zpow_zero, Complex.ofReal_one]

theorem cdiag_mul {t : ℝ} (ht : t ≠ 0) : cdiag k r t * cdiag k r t⁻¹ = 1 := by
  rw [cdiag, cdiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; exact dvec_mul_inv ht i

theorem cdiag_mul' {t : ℝ} (ht : t ≠ 0) : cdiag k r t⁻¹ * cdiag k r t = 1 := by
  have := cdiag_mul (k := k) (r := r) (inv_ne_zero ht)
  rwa [inv_inv] at this

theorem cdiag_inv {t : ℝ} (ht : t ≠ 0) : (cdiag k r t)⁻¹ = cdiag k r t⁻¹ :=
  Matrix.inv_eq_right_inv (cdiag_mul ht)

theorem conj_apply (t : ℝ) (g : 𝕄) (i j : Fin (2 * r + k + 1)) :
    (cdiag k r t * g * cdiag k r t⁻¹) i j = dvec t i * g i j * dvec t⁻¹ j := by
  rw [cdiag, cdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem cdiag_mem_UH {t : ℝ} (ht : t ≠ 0) : cdiag k r t ∈ UH (Hpk k r) := by
  show (cdiag k r t)ᴴ * Hpk k r * cdiag k r t = Hpk k r
  ext i j
  rw [cdiag, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Hpk_apply]
  split_ifs with h
  · subst h
    have e : star (dvec (k := k) (r := r) t) i * dvec t (piI k r i) = 1 := by
      rw [Pi.star_apply, dvec, dvec, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← zpow_add₀ ht, expo_add_piI, zpow_zero, Complex.ofReal_one]
    calc star (dvec (k := k) (r := r) t) i * epsI k r i * dvec t (piI k r i)
        = epsI k r i * (star (dvec (k := k) (r := r) t) i * dvec t (piI k r i)) := by ring
      _ = epsI k r i := by rw [e, mul_one]
  · simp

theorem cdiag_conj_WB {t : ℝ} (ht : t ≠ 0) {a : 𝕄} (ha : WB k r a) :
    cdiag k r t * a * cdiag k r t⁻¹ = a := by
  ext i j
  rw [conj_apply]
  by_cases hij : inW k r i ∧ inW k r j
  · rw [dvec_of_inW hij.1, dvec_of_inW hij.2, one_mul, mul_one]
  · rw [ha i j hij]
    split_ifs with h
    · subst h; rw [mul_one, dvec_mul_inv ht]
    · rw [mul_zero, zero_mul]

theorem cdiag_conj_N {t : ℝ} (ht : t ≠ 0) {m : 𝕄} (hm : m ∈ Nset k r) :
    cdiag k r t * m * cdiag k r t⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hm ⊢
  refine ⟨mul_mem_UH (mul_mem_UH (cdiag_mem_UH ht) hm.1) (cdiag_mem_UH (inv_ne_zero ht)),
    fun i j hj hi => ?_⟩
  rw [conj_apply, hm.2 i j hj hi]
  split_ifs with h
  · subst h; rw [mul_one, dvec_mul_inv ht]
  · rw [mul_zero, zero_mul]

variable {z : Fin (2 * r + k + 1) → ℂ}

theorem cdiag_conj_S {t : ℝ} (ht : t ≠ 0) {g : 𝕄} (hg : g ∈ Sset k r z) :
    cdiag k r t * g * cdiag k r t⁻¹ ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  refine ⟨h, hh, cdiag k r t * m * cdiag k r t⁻¹, cdiag_conj_N ht hm, ?_⟩
  calc cdiag k r t * (h * m) * cdiag k r t⁻¹
      = (cdiag k r t * h * cdiag k r t⁻¹) * (cdiag k r t * m * cdiag k r t⁻¹) := by
        rw [show (cdiag k r t * h * cdiag k r t⁻¹) * (cdiag k r t * m * cdiag k r t⁻¹) =
          cdiag k r t * h * (cdiag k r t⁻¹ * cdiag k r t) * m * cdiag k r t⁻¹ by
            simp only [Matrix.mul_assoc], cdiag_mul' ht, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = h * (cdiag k r t * m * cdiag k r t⁻¹) := by rw [cdiag_conj_WB ht (wb_of_mem_UW hh)]

theorem cdiag_normalises {t : ℝ} (ht : t ≠ 0) (g : 𝕄) :
    cdiag k r t * g * (cdiag k r t)⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z := by
  rw [cdiag_inv ht]
  refine ⟨fun h => ?_, cdiag_conj_S ht⟩
  have := cdiag_conj_S (z := z) (inv_ne_zero ht) h
  rwa [inv_inv, show cdiag k r t⁻¹ * (cdiag k r t * g * cdiag k r t⁻¹) * cdiag k r t =
      (cdiag k r t⁻¹ * cdiag k r t) * g * (cdiag k r t⁻¹ * cdiag k r t) by
        simp only [Matrix.mul_assoc], cdiag_mul' ht, Matrix.one_mul, Matrix.mul_one] at this

theorem norm_dvec_mul (t : ℝ) (ht : 0 < t) (x : ℂ) (i j : Fin (2 * r + k + 1)) :
    ‖dvec (k := k) (r := r) t i * x * dvec t⁻¹ j‖ = t ^ (expo k r i - expo k r j) * ‖x‖ := by
  rw [dvec, dvec, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (zpow_pos ht _), abs_of_pos (zpow_pos (inv_pos.2 ht) _),
    _root_.inv_zpow', sub_eq_add_neg, zpow_add₀ ht.ne']
  ring

theorem unipotent_radical_contracting : NContract := by
  intro k r z _hz n hn ε hε
  set M : ℝ := ∑ i, ∑ j, ‖n i j‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hnM : ∀ i j, ‖n i j‖ ≤ M := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖n i j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖n i j‖)
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
  set t : ℝ := min 1 (ε / (M + 1)) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos hε (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htM : t * M ≤ ε := by
    have h1 : t ≤ ε / (M + 1) := min_le_right _ _
    have h2 : ε / (M + 1) * M ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    exact (mul_le_mul_of_nonneg_right h1 hM0).trans h2
  refine ⟨cdiag k r t, ⟨⟨cdiag k r t, cdiag k r t⁻¹, cdiag_mul ht0.ne', cdiag_mul' ht0.ne'⟩, rfl⟩,
    cdiag_normalises ht0.ne', fun i j => ?_⟩
  rw [cdiag_inv ht0.ne', Matrix.sub_apply, conj_apply, Matrix.one_apply]
  by_cases hji : j.val ≤ i.val
  · rw [n_ut hn i j hji]
    split_ifs with h
    · subst h; rw [mul_one, dvec_mul_inv ht0.ne', sub_self, norm_zero]; exact hε.le
    · rw [mul_zero, zero_mul, sub_zero, norm_zero]; exact hε.le
  · have hij : i.val < j.val := by omega
    have hne : i ≠ j := by intro e; subst e; omega
    rw [if_neg hne, sub_zero]
    by_cases hW : inW k r i ∧ inW k r j
    · have hn' := ((mem_Nset_iff n).1 hn).2 i j hW.2.2 (by unfold inW at hW; omega)
      rw [hn', if_neg hne, mul_zero, zero_mul, norm_zero]; exact hε.le
    · rw [norm_dvec_mul t ht0]
      have hexp := expo_lt (k := k) (r := r) hij hW
      have h1 : t ^ (expo k r i - expo k r j) ≤ t ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ ht0 ht1 (by omega)
      rw [zpow_one] at h1
      calc t ^ (expo k r i - expo k r j) * ‖n i j‖ ≤ t * M :=
            mul_le_mul h1 (hnM i j) (norm_nonneg _) ht0.le
        _ ≤ ε := htM

end CompanionTheory.D.Upq.QuotSetU
