import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ

section

noncomputable section

open Formalism.REAL (UJ KG toM)
open GlobalTheory.PsCo.Pc1 (rM Mode)

namespace GlobalTheory.PsCo.PcdConjLow

open Matrix

variable {n : ℕ} {ε : Fin n → Bool}

lemma jm_diag (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl

lemma jm_ne (ε : Fin n → Bool) (a : Fin n) : (if ε a then (1 : ℂ) else -1) ≠ 0 := by
  split_ifs <;> norm_num

lemma inUJ_toM (g : UJ ε) : (toM g)ᴴ * Formalism.REAL.Jm ε * toM g = Formalism.REAL.Jm ε := g.2

lemma toM_mul_inv (g : UJ ε) : toM g * toM g⁻¹ = 1 := by
  simp [toM]

lemma mul_J_conj (Y : Matrix (Fin n) (Fin n) ℂ) (h : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε) :
    Y * Formalism.REAL.Jm ε * Yᴴ = Formalism.REAL.Jm ε := by
  have J2 := Formalism.REAL.Jm_mul_self ε
  have h1 : Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε * Y = 1 := by
    rw [show Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε * (Yᴴ * Formalism.REAL.Jm ε * Y) by
      simp only [Matrix.mul_assoc], h, J2]
  have h2 : Y * (Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp h1
  calc Y * Formalism.REAL.Jm ε * Yᴴ = Y * (Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by
        simp only [Matrix.mul_assoc, J2, Matrix.mul_one]
    _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.one_mul]

lemma diag_unit (d : Fin n → ℂ)
    (h : (diagonal d)ᴴ * Formalism.REAL.Jm ε * diagonal d = Formalism.REAL.Jm ε) (i : Fin n) :
    star (d i) * d i = 1 := by
  rw [jm_diag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal] at h
  have h1 := congrFun (congrFun h i) i
  simp only [Matrix.diagonal_apply_eq, Pi.star_apply] at h1
  have h2 : star (d i) * d i * (if ε i then (1 : ℂ) else -1) = 1 * (if ε i then (1 : ℂ) else -1) := by
    rw [one_mul]; linear_combination h1
  exact mul_right_cancel₀ (jm_ne ε i) h2

lemma diag_mem_Kset (d : Fin n → ℂ)
    (h : (diagonal d)ᴴ * Formalism.REAL.Jm ε * diagonal d = Formalism.REAL.Jm ε) : diagonal d ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    simp only [Pi.star_apply]
    rw [mul_comm]
    exact diag_unit d h i
  · rw [jm_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    ring

theorem diag_mem_K (s : UJ ε) (d : Fin n → ℂ) (hs : toM s = Matrix.diagonal d) : s ∈ KG ε := by
  rw [Formalism.REAL.mem_KG, hs]
  exact diag_mem_Kset d (by rw [← hs]; exact inUJ_toM s)

lemma mat_core (Y Yi : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (hd : Function.Injective d)
    (hYYi : Y * Yi = 1) (hy : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε)
    (hSK : diagonal d ∈ Formalism.REAL.Kset ε) (hK : Yi * diagonal d * Y ∈ Formalism.REAL.Kset ε) :
    Y ∈ Formalism.REAL.Kset ε := by
  have J2 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have J2' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * X) = X := by
    intro X; rw [← Matrix.mul_assoc, J2, Matrix.one_mul]
  have hYiY : Yi * Y = 1 := mul_eq_one_comm.mp hYYi
  have hYi : Yi = Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    have h1 : Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε * Y = 1 := by
      rw [show Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε * (Yᴴ * Formalism.REAL.Jm ε * Y) by
        simp only [Matrix.mul_assoc], hy, J2]
    calc Yi = Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε * Y * Yi := by rw [h1, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc _ Y Yi, hYYi, Matrix.mul_one]
  set k := Yi * Matrix.diagonal d * Y with hk
  have hD : Y * k * Yi = Matrix.diagonal d := by
    rw [hk, show Y * (Yi * Matrix.diagonal d * Y) * Yi = (Y * Yi) * Matrix.diagonal d * (Y * Yi) by
      simp only [Matrix.mul_assoc], hYYi, Matrix.one_mul, Matrix.mul_one]

  have hMD : Y * Formalism.REAL.Jm ε * Yi * Matrix.diagonal d = Matrix.diagonal d * (Y * Formalism.REAL.Jm ε * Yi) := by
    rw [← hD]
    calc Y * Formalism.REAL.Jm ε * Yi * (Y * k * Yi) = Y * (Formalism.REAL.Jm ε * k) * Yi := by
          rw [show Y * Formalism.REAL.Jm ε * Yi * (Y * k * Yi) = Y * Formalism.REAL.Jm ε * (Yi * Y) * k * Yi by
            simp only [Matrix.mul_assoc], hYiY, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Y * (k * Formalism.REAL.Jm ε) * Yi := by rw [hK.2]
      _ = Y * k * Yi * (Y * Formalism.REAL.Jm ε * Yi) := by
          rw [show Y * k * Yi * (Y * Formalism.REAL.Jm ε * Yi) = Y * k * (Yi * Y) * Formalism.REAL.Jm ε * Yi by
            simp only [Matrix.mul_assoc], hYiY, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  obtain ⟨M, hMdef⟩ : ∃ M, Y * Formalism.REAL.Jm ε * Yi = M := ⟨_, rfl⟩
  have hMM : Y * Formalism.REAL.Jm ε * Yi * (Y * Formalism.REAL.Jm ε * Yi) = 1 := by
    rw [show Y * Formalism.REAL.Jm ε * Yi * (Y * Formalism.REAL.Jm ε * Yi) = Y * (Formalism.REAL.Jm ε * ((Yi * Y) * (Formalism.REAL.Jm ε * Yi))) by
      simp only [Matrix.mul_assoc], hYiY, Matrix.one_mul, J2', hYYi]
  have hP : Y * Yᴴ = Y * Formalism.REAL.Jm ε * Yi * Formalism.REAL.Jm ε := by
    rw [hYi]
    simp only [Matrix.mul_assoc, J2', J2, Matrix.mul_one]
  rw [hMdef] at hMD hMM hP
  have hMoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have h1 := congrFun (congrFun hMD i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : (d i - d j) * M i j = 0 := by linear_combination -h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hd.ne hij))

  have hMJ : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
    ext i j
    rw [jm_diag, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = j
    · rw [← hij]; ring
    · rw [hMoff i j hij]; ring
  have hPP : Y * Yᴴ * (Y * Yᴴ) = 1 := by
    calc Y * Yᴴ * (Y * Yᴴ) = M * Formalism.REAL.Jm ε * (M * Formalism.REAL.Jm ε) := by rw [hP]
      _ = M * (Formalism.REAL.Jm ε * M) * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc]
      _ = M * (M * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [← hMJ]
      _ = (M * M) * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMM, J2, Matrix.one_mul]
  have hPoff : ∀ i j, i ≠ j → (Y * Yᴴ) i j = 0 := by
    intro i j hij
    rw [hP, jm_diag, Matrix.mul_diagonal, hMoff i j hij, zero_mul]
  have hPdiag : ∀ i, (Y * Yᴴ) i i = ((∑ j, ‖Y i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']
  have hP1 : Y * Yᴴ = 1 := by
    ext i j
    by_cases hij : i = j
    · rw [← hij]
      have h1 := congrFun (congrFun hPP i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun b _ hb => by rw [hPoff i b (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), hPdiag] at h1
      rw [hPdiag, Matrix.one_apply_eq]
      have h0 : (0 : ℝ) ≤ ∑ j, ‖Y i j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
      have h2 : (∑ j, ‖Y i j‖ ^ 2) * (∑ j, ‖Y i j‖ ^ 2) = 1 := by
        rw [Matrix.one_apply_eq] at h1
        exact_mod_cast h1
      have h3 : ∑ j, ‖Y i j‖ ^ 2 = 1 := by nlinarith
      rw [h3]; simp
    · rw [hPoff i j hij, Matrix.one_apply_ne hij]
  have hYh : Yᴴ = Yi := by
    calc Yᴴ = Yi * Y * Yᴴ := by rw [hYiY, Matrix.one_mul]
      _ = Yi := by rw [Matrix.mul_assoc, hP1, Matrix.mul_one]
  have hY2 : Y = Formalism.REAL.Jm ε * (Y * Formalism.REAL.Jm ε) := by
    have h1 := congrArg Matrix.conjTranspose (hYh.trans hYi)
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Formalism.REAL.Jm_conjTranspose] at h1
    exact h1
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hP1
  · conv_lhs => rw [hY2]
    simp only [Matrix.mul_assoc, J2, Matrix.mul_one]

theorem mem_K_of_conj (s y : UJ ε) (d : Fin n → ℂ) (hs : toM s = Matrix.diagonal d)
    (hd : Function.Injective d) (h : y⁻¹ * s * y ∈ KG ε) : y ∈ KG ε := by
  rw [Formalism.REAL.mem_KG] at h ⊢
  have e : toM (y⁻¹ * s * y) = toM y⁻¹ * Matrix.diagonal d * toM y := by rw [← hs]; rfl
  rw [e] at h
  exact mat_core (toM y) (toM y⁻¹) d hd (toM_mul_inv y) (inUJ_toM y)
    (diag_mem_Kset d (by rw [← hs]; exact inUJ_toM s)) h

end GlobalTheory.PsCo.PcdConjLow

end
end

section

noncomputable section

open Formalism.REAL (UJ KG toM Jm Kset inUJ)
open GlobalTheory.PsCo.Pc1 (rM Mode)
open scoped Matrix

namespace GlobalTheory.PsCo.PcdConjLow

variable {n : ℕ} {ε : Fin n → Bool}

theorem offDiagonalBlockSqNorm_eq_sum_ite (g : Matrix (Fin n) (Fin n) ℂ) :
    rM ε g = ∑ i, ∑ j, if ε i = true ∧ ε j = false then ‖g i j‖ ^ 2 else 0 := by
  rw [GlobalTheory.PsCo.Pc1.rM, ← Finset.sum_subtype (Finset.univ.filter fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false)
    (by simp) (fun x => ‖g x.1 x.2‖ ^ 2), Finset.sum_filter, Fintype.sum_prod_type]

theorem continuous_rM : Continuous fun g : UJ ε => rM ε (toM g) := by
  have h : Continuous fun g : UJ ε => toM g := Units.continuous_val.comp continuous_subtype_val
  unfold GlobalTheory.PsCo.Pc1.rM
  exact continuous_finset_sum _ fun x _ => (h.matrix_elem x.1.1 x.1.2).norm.pow 2

theorem mul_signMatrix_apply (g : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (g * Jm ε) a b = g a b * (if ε b then 1 else -1) := by
  rw [jm_diag, Matrix.mul_diagonal]

theorem signMatrix_mul_apply (g : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * g) a b = (if ε a then 1 else -1) * g a b := by
  rw [jm_diag, Matrix.diagonal_mul]

theorem entry_eq_zero_of_commute_signMatrix_diffSign {g : Matrix (Fin n) (Fin n) ℂ} (h : g * Jm ε = Jm ε * g) (a b : Fin n) (hab : ε a ≠ ε b) :
    g a b = 0 := by
  have h1 := congrFun (congrFun h a) b
  rw [mul_signMatrix_apply, signMatrix_mul_apply] at h1
  have h2 : g a b * ((if ε b then (1 : ℂ) else -1) - (if ε a then 1 else -1)) = 0 := by
    rw [mul_sub, h1]; ring
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exfalso
    cases ha : ε a <;> cases hb : ε b <;> first
      | exact absurd (ha.trans hb.symm) hab
      | (rw [ha, hb] at h3; norm_num at h3)

theorem rM_of_mem_K (g : UJ ε) (h : g ∈ KG ε) : rM ε (toM g) = 0 := by
  rw [Formalism.REAL.mem_KG] at h
  rw [offDiagonalBlockSqNorm_eq_sum_ite]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hij
  · rw [entry_eq_zero_of_commute_signMatrix_diffSign h.2 i j (by rw [hij.1, hij.2]; decide)]; simp
  · rfl

private lemma sum_sq_norm_column_eq_conjTranspose_mul_diag (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    ((∑ i, ‖A i j‖ ^ 2 : ℝ) : ℂ) = (Aᴴ * A) j j := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']

theorem sum_sqNorm_column_unitary_mul (u M : Matrix (Fin n) (Fin n) ℂ) (hu : star u * u = 1) (j : Fin n) :
    ∑ i, ‖(u * M) i j‖ ^ 2 = ∑ i, ‖M i j‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_sq_norm_column_eq_conjTranspose_mul_diag, sum_sq_norm_column_eq_conjTranspose_mul_diag, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ,
    ← Matrix.star_eq_conjTranspose u, hu, Matrix.one_mul]

theorem offDiagonalBlockSqNorm_eq_sum_columns (g : Matrix (Fin n) (Fin n) ℂ) :
    rM ε g = ∑ j, if ε j = false then ∑ i, ‖(Matrix.of fun a b => if ε a = true then g a b else 0) i j‖ ^ 2 else 0 := by
  rw [offDiagonalBlockSqNorm_eq_sum_ite, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : ε j = false
  · rw [if_pos hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ε i = true <;> simp [hi, hj]
  · rw [if_neg hj]
    exact Finset.sum_eq_zero fun i _ => by simp [hj]

theorem rM_mul_left (t x : UJ ε) (ht : t ∈ KG ε) : rM ε (toM (t * x)) = rM ε (toM x) := by
  have hK : toM t ∈ Kset ε := (Formalism.REAL.mem_KG ε t).1 ht
  have hm : toM (t * x) = toM t * toM x := rfl
  rw [offDiagonalBlockSqNorm_eq_sum_columns, offDiagonalBlockSqNorm_eq_sum_columns, hm]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · have key : (Matrix.of fun a b => if ε a = true then (toM t * toM x) a b else 0)
        = toM t * Matrix.of fun a b => if ε a = true then toM x a b else 0 := by
      ext a b
      simp only [Matrix.of_apply, Matrix.mul_apply]
      split_ifs with ha
      · refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hc : ε c = true
        · simp [hc]
        · rw [entry_eq_zero_of_commute_signMatrix_diffSign hK.2 a c (by rw [ha]; exact fun h => hc h.symm)]; simp [hc]
      · symm
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases hc : ε c = true
        · rw [entry_eq_zero_of_commute_signMatrix_diffSign hK.2 a c (by rw [hc]; exact ha)]; simp
        · simp [hc]
    rw [key, sum_sqNorm_column_unitary_mul _ _ (Matrix.mem_unitaryGroup_iff'.1 hK.1)]
  · rfl

theorem signForm_conjTranspose_diag_eq_signed_sum_row (N : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    (N * Jm ε * Nᴴ) a a = ((∑ c, (if ε c = true then (1 : ℝ) else -1) * ‖N a c‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_signMatrix_apply, Matrix.conjTranspose_apply, Complex.star_def]
  have h := Complex.mul_conj' (N a c)
  split_ifs
  · push_cast; linear_combination h
  · push_cast; linear_combination -h

theorem conjTranspose_signForm_diag_eq_signed_sum_col (N : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    (Nᴴ * Jm ε * N) c c = ((∑ i, (if ε i = true then (1 : ℝ) else -1) * ‖N i c‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_signMatrix_apply, Matrix.conjTranspose_apply, Complex.star_def]
  have h := Complex.conj_mul' (N i c)
  split_ifs
  · push_cast; linear_combination h
  · push_cast; linear_combination -h

theorem signMatrix_diag_apply (a : Fin n) : Jm ε a a = (((if ε a = true then (1 : ℝ) else -1) : ℝ) : ℂ) := by
  rw [jm_diag, Matrix.diagonal_apply_eq]
  split_ifs <;> simp

theorem mem_K_of_rM (g : UJ ε) (h : rM ε (toM g) = 0) : g ∈ KG ε := by
  have hG : (toM g)ᴴ * Jm ε * toM g = Jm ε := inUJ_toM g
  have hG' : toM g * Jm ε * (toM g)ᴴ = Jm ε := mul_J_conj (toM g) hG
  have J2 := Formalism.REAL.Jm_mul_self ε
  have hup : ∀ a b, ε a = true → ε b = false → toM g a b = 0 := by
    intro a b ha hb
    rw [offDiagonalBlockSqNorm_eq_sum_ite] at h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h a (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 b (Finset.mem_univ _)
    rw [if_pos ⟨ha, hb⟩] at h2
    simpa using h2
  have hcol : ∀ c, ∑ i, (if ε i = true then (1 : ℝ) else -1) * ‖toM g i c‖ ^ 2
      = if ε c = true then 1 else -1 := by
    intro c
    apply Complex.ofReal_injective
    rw [← conjTranspose_signForm_diag_eq_signed_sum_col (toM g) c, hG, signMatrix_diag_apply]
  have hrow : ∀ a, ∑ c, (if ε c = true then (1 : ℝ) else -1) * ‖toM g a c‖ ^ 2
      = if ε a = true then 1 else -1 := by
    intro a
    apply Complex.ofReal_injective
    rw [← signForm_conjTranspose_diag_eq_signed_sum_row (toM g) a, hG', signMatrix_diag_apply]
  have hsplit : ∀ x : Fin n → ℝ, ∑ i, (if ε i = true then (1 : ℝ) else -1) * x i
      = ∑ i, (if ε i = true then x i else 0) - ∑ i, (if ε i = false then x i else 0) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp
  have hc1 : ∀ c, ε c = false → ∑ i, (if ε i = false then ‖toM g i c‖ ^ 2 else 0) = 1 := by
    intro c hc
    have e := hcol c
    rw [hsplit (fun i => ‖toM g i c‖ ^ 2), if_neg (by simp [hc])] at e
    have e0 : ∑ i, (if ε i = true then ‖toM g i c‖ ^ 2 else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        by_cases hi : ε i = true
        · simp [hi, hup i c hi hc]
        · simp [hi]
    linarith
  have hr1 : ∀ a, ε a = false → ∑ c, (if ε c = true then ‖toM g a c‖ ^ 2 else 0)
      - ∑ c, (if ε c = false then ‖toM g a c‖ ^ 2 else 0) = -1 := by
    intro a ha
    have e := hrow a
    rw [hsplit (fun c => ‖toM g a c‖ ^ 2), if_neg (by simp [ha])] at e
    exact e
  have e1 : ∑ a, (if ε a = false then ∑ c, (if ε c = false then ‖toM g a c‖ ^ 2 else 0) else 0)
      = ∑ a, (if ε a = false then (1 : ℝ) else 0) := by
    rw [show (∑ a, (if ε a = false then ∑ c, (if ε c = false then ‖toM g a c‖ ^ 2 else 0) else 0))
        = ∑ a, ∑ c, (if ε a = false then (if ε c = false then ‖toM g a c‖ ^ 2 else 0) else 0) from
      Finset.sum_congr rfl fun a _ => by by_cases ha : ε a = false <;> simp [ha], Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ε c = false
    · rw [if_pos hc, ← hc1 c hc]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : ε a = false <;> simp [ha, hc]
    · rw [if_neg hc]
      exact Finset.sum_eq_zero fun a _ => by by_cases ha : ε a = false <;> simp [ha, hc]
  have e2 : ∑ a, (if ε a = false then ∑ c, (if ε c = true then ‖toM g a c‖ ^ 2 else 0) else 0)
      - ∑ a, (if ε a = false then ∑ c, (if ε c = false then ‖toM g a c‖ ^ 2 else 0) else 0)
      = ∑ a, (if ε a = false then (-1 : ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : ε a = false
    · simp only [if_pos ha]; exact hr1 a ha
    · simp [ha]
  have e3 : ∑ a, (if ε a = false then (-1 : ℝ) else 0) = -∑ a, (if ε a = false then (1 : ℝ) else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : ε a = false <;> simp [ha]
  have hsum : ∑ a, (if ε a = false then ∑ c, (if ε c = true then ‖toM g a c‖ ^ 2 else 0) else 0) = 0 := by
    linarith
  have hlow : ∀ a c, ε a = false → ε c = true → toM g a c = 0 := by
    intro a c ha hc
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hsum a (Finset.mem_univ _)
    rw [if_pos ha] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by positivity)).1 h1 c (Finset.mem_univ _)
    rw [if_pos hc] at h2
    simpa using h2
  have hcomm : toM g * Jm ε = Jm ε * toM g := by
    ext a b
    rw [mul_signMatrix_apply, signMatrix_mul_apply]
    cases ha : ε a <;> cases hb : ε b <;> simp [hup a b, hlow a b, ha, hb]
  have hu : (toM g)ᴴ * toM g = 1 := by
    calc (toM g)ᴴ * toM g = (toM g)ᴴ * toM g * (Jm ε * Jm ε) := by rw [J2, Matrix.mul_one]
      _ = (toM g)ᴴ * (toM g * Jm ε) * Jm ε := by simp only [Matrix.mul_assoc]
      _ = Jm ε * Jm ε := by rw [hcomm, ← Matrix.mul_assoc, hG]
      _ = 1 := J2
  rw [Formalism.REAL.mem_KG]
  exact ⟨by rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact hu, hcomm⟩

end GlobalTheory.PsCo.PcdConjLow

end
end

section

noncomputable section

open scoped Matrix
open Formalism.REAL (UJ KG toM)
open GlobalTheory.PsCo.Pc1 (rM Mode)

namespace GlobalTheory.PsCo.PcdConjLow

namespace C3

variable {n : ℕ} {ε : Fin n → Bool}

def sg (ε : Fin n → Bool) (i : Fin n) : ℝ := if ε i then 1 else -1

lemma sg_sq (i : Fin n) : sg ε i * sg ε i = 1 := by
  unfold sg
  split_ifs <;> norm_num

lemma Jm_eq : Formalism.REAL.Jm ε = Matrix.diagonal fun i => ((sg ε i : ℝ) : ℂ) := by
  unfold Formalism.REAL.Jm sg
  congr 1
  ext i
  split_ifs <;> simp

lemma re_star_mul_real_mul_eq_sqNorm (z : ℂ) (r : ℝ) : (star z * (r : ℂ) * z).re = r * ‖z‖ ^ 2 := by
  have h : star z * (r : ℂ) * z = ((r * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def]
    push_cast
    linear_combination (r : ℂ) * Complex.conj_mul' z
  rw [h, Complex.ofReal_re]

lemma re_mul_real_mul_star_eq_sqNorm (z : ℂ) (r : ℝ) : (z * (r : ℂ) * star z).re = r * ‖z‖ ^ 2 := by
  have h : z * (r : ℂ) * star z = ((r * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def]
    push_cast
    linear_combination (r : ℂ) * Complex.mul_conj' z
  rw [h, Complex.ofReal_re]

lemma col_rel (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) (j : Fin n) :
    ∑ i, sg ε i * ‖g i j‖ ^ 2 = sg ε j := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h2 : ((gᴴ * Formalism.REAL.Jm ε * g) j j).re = (Formalism.REAL.Jm ε j j).re := by rw [h]
  rw [Jm_eq, Matrix.mul_apply, Matrix.diagonal_apply_eq, Complex.ofReal_re, Complex.re_sum] at h2
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, re_star_mul_real_mul_eq_sqNorm] at h2
  exact h2

lemma row_rel (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) (i : Fin n) :
    ∑ j, sg ε j * ‖g i j‖ ^ 2 = sg ε i := by
  have h : g * Formalism.REAL.Jm ε * gᴴ = Formalism.REAL.Jm ε := mul_J_conj g hg
  have h2 : ((g * Formalism.REAL.Jm ε * gᴴ) i i).re = (Formalism.REAL.Jm ε i i).re := by rw [h]
  rw [Jm_eq, Matrix.mul_apply, Matrix.diagonal_apply_eq, Complex.ofReal_re, Complex.re_sum] at h2
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, re_mul_real_mul_star_eq_sqNorm] at h2
  exact h2

lemma rM_eq_sum (g : Matrix (Fin n) (Fin n) ℂ) :
    rM ε g = ∑ i, ∑ j, ‖g i j‖ ^ 2 * (((1 - sg ε i * sg ε j) + (sg ε i - sg ε j)) / 4) := by
  rw [offDiagonalBlockSqNorm_eq_sum_ite]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold sg
  cases hi : ε i <;> cases hj : ε j <;> norm_num [hi, hj]

lemma total_eq (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) :
    ∑ i, ∑ j, ‖g i j‖ ^ 2 = n + 4 * rM ε g := by
  have hr := row_rel g hg
  have hc := col_rel g hg
  have hA : ∑ i, ∑ j, sg ε i * ‖g i j‖ ^ 2 = ∑ j, sg ε j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hc j
  have hC : ∑ i, sg ε i * sg ε i = n := by simp [sg_sq]
  rw [rM_eq_sum]
  have h1 : ∑ i, ∑ j, ‖g i j‖ ^ 2 * (((1 - sg ε i * sg ε j) + (sg ε i - sg ε j)) / 4)
      = ∑ i, ((∑ j, ‖g i j‖ ^ 2) - sg ε i * (∑ j, sg ε j * ‖g i j‖ ^ 2)
        + (∑ j, sg ε i * ‖g i j‖ ^ 2) - (∑ j, sg ε j * ‖g i j‖ ^ 2)) / 4 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  simp only [hr]
  rw [← Finset.sum_div]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hA, hC]
  ring

lemma entry_le (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) (i j : Fin n) :
    ‖g i j‖ ^ 2 ≤ n + 4 * rM ε g := by
  rw [← total_eq g hg]
  exact le_trans (Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))

lemma continuous_rM_mat : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => rM ε g := by
  unfold GlobalTheory.PsCo.Pc1.rM
  exact continuous_finset_sum _ fun x _ => (continuous_id.matrix_elem x.1.1 x.1.2).norm.pow 2

end C3

variable {n : ℕ} {ε : Fin n → Bool}

open C3 in
theorem isCompact_rM_le (c : ℝ) : IsCompact {g : UJ ε | rM ε (toM g) ≤ c} := by
  have J2 := Formalism.REAL.Jm_mul_self ε
  let S : Set (Matrix (Fin n) (Fin n) ℂ) := {G | Formalism.REAL.inUJ ε G ∧ rM ε G ≤ c}
  have hScl : IsClosed S := by
    refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_le continuous_rM_mat continuous_const)
    exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  have hSc : IsCompact S := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) (Real.sqrt (n + 4 * c))) hScl ?_
    intro G hG
    refine Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have h : ‖G i j‖ ^ 2 ≤ n + 4 * c := (entry_le G hG.1 i j).trans (by linarith [hG.2])
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)
  have hinv : ∀ G ∈ S, G * (Formalism.REAL.Jm ε * Gᴴ * Formalism.REAL.Jm ε) = 1 ∧
      Formalism.REAL.Jm ε * Gᴴ * Formalism.REAL.Jm ε * G = 1 := by
    intro G hG
    have h1 : Gᴴ * Formalism.REAL.Jm ε * G = Formalism.REAL.Jm ε := hG.1
    have h2 : Formalism.REAL.Jm ε * Gᴴ * Formalism.REAL.Jm ε * G = 1 := by
      rw [show Formalism.REAL.Jm ε * Gᴴ * Formalism.REAL.Jm ε * G = Formalism.REAL.Jm ε * (Gᴴ * Formalism.REAL.Jm ε * G) by
        simp only [Matrix.mul_assoc], h1, J2]
    exact ⟨mul_eq_one_comm.mp h2, h2⟩
  let F : S → UJ ε := fun G =>
    ⟨⟨G.1, Formalism.REAL.Jm ε * G.1ᴴ * Formalism.REAL.Jm ε, (hinv G.1 G.2).1, (hinv G.1 G.2).2⟩, G.2.1⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val,
      (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const⟩
  have e : {g : UJ ε | rM ε (toM g) ≤ c} = F '' Set.univ := by
    ext g
    constructor
    · intro hg
      exact ⟨⟨toM g, inUJ_toM g, hg⟩, trivial, Subtype.ext (Units.ext rfl)⟩
    · rintro ⟨G, -, rfl⟩
      exact G.2.2
  rw [e]
  exact (isCompact_iff_isCompact_univ.mp hSc).image hF

end GlobalTheory.PsCo.PcdConjLow

end
end

section

noncomputable section

open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.PsCo.PcdConjLow

theorem isRegSS_of_diag {n : ℕ} {ε : Fin n → Bool} (s : UJ ε) (d : Fin n → ℂ)
    (hs : toM s = Matrix.diagonal d) (hd : Function.Injective d) : GlobalTheory.Orb.IsRegSS (GlobalTheory.Orb.ujMat ε s) := by
  have e : GlobalTheory.Orb.ujMat ε s = toM s := rfl
  rw [e, hs, GlobalTheory.Orb.IsRegSS, Matrix.charpoly_diagonal]
  exact (Polynomial.separable_prod_X_sub_C_iff').2 fun i _ j _ h => hd h

end GlobalTheory.PsCo.PcdConjLow

end
end

section

noncomputable section

open Formalism.REAL (UJ KG toM)
open GlobalTheory.PsCo.Pc1 (rM)

namespace GlobalTheory.PsCo.Pcd

theorem stConjLow : GlobalTheory.PsCo.Pc3.StConjLow := by
  intro n ε s d hs hd δ hδ
  have hreg := GlobalTheory.PsCo.PcdConjLow.isRegSS_of_diag s d hs hd
  obtain ⟨C, hC, hCp⟩ := GlobalTheory.Orb.isProperOrbit_realUJ hreg _ (GlobalTheory.PsCo.PcdConjLow.isCompact_rM_le (ε := ε) 1)
  have hconj : ∀ t ∈ GlobalTheory.Orb.cent s, t⁻¹ * s * t = s := by
    intro t ht
    have h1 : t * s = s * t := GlobalTheory.Orb.mem_cent.1 ht
    rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcK : ∀ t ∈ GlobalTheory.Orb.cent s, t ∈ KG ε := by
    intro t ht
    refine GlobalTheory.PsCo.PcdConjLow.mem_K_of_conj s t d hs hd ?_
    rw [hconj t ht]
    exact GlobalTheory.PsCo.PcdConjLow.diag_mem_K s d hs
  have hφc : Continuous fun x : UJ ε => rM ε (toM (x⁻¹ * s * x)) :=
    GlobalTheory.PsCo.PcdConjLow.continuous_rM.comp ((continuous_inv.mul continuous_const).mul continuous_id)
  have hφ0 : ∀ x : UJ ε, 0 ≤ rM ε (toM (x⁻¹ * s * x)) := fun x => by
    unfold GlobalTheory.PsCo.Pc1.rM; positivity
  have hD : IsCompact (C ∩ {x : UJ ε | δ ≤ rM ε (toM x)}) :=
    hC.inter_right (isClosed_le continuous_const GlobalTheory.PsCo.PcdConjLow.continuous_rM)
  have key : ∀ x : UJ ε, rM ε (toM (x⁻¹ * s * x)) ≤ 1 → δ < rM ε (toM x) →
      ∃ y ∈ C ∩ {x : UJ ε | δ ≤ rM ε (toM x)}, rM ε (toM (y⁻¹ * s * y)) = rM ε (toM (x⁻¹ * s * x)) := by
    intro x hx1 hx2
    obtain ⟨t, ht, htC⟩ := hCp x hx1
    refine ⟨t * x, ⟨htC, ?_⟩, ?_⟩
    · show δ ≤ rM ε (toM (t * x))
      rw [GlobalTheory.PsCo.PcdConjLow.rM_mul_left t x (hcK t ht)]
      exact hx2.le
    · have e : (t * x)⁻¹ * s * (t * x) = x⁻¹ * (t⁻¹ * s * t) * x := by group
      rw [e, hconj t ht]
  rcases (C ∩ {x : UJ ε | δ ≤ rM ε (toM x)}).eq_empty_or_nonempty with hDe | hDn
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    by_contra hc
    push_neg at hc
    obtain ⟨y, hy, -⟩ := key x hx hc
    rw [hDe] at hy
    exact hy
  · obtain ⟨x0, hx0, hmin⟩ := hD.exists_isMinOn hDn hφc.continuousOn
    have hpos : 0 < rM ε (toM (x0⁻¹ * s * x0)) := by
      rcases (hφ0 x0).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : x0⁻¹ * s * x0 ∈ KG ε := GlobalTheory.PsCo.PcdConjLow.mem_K_of_rM _ h.symm
        have h2 := GlobalTheory.PsCo.PcdConjLow.mem_K_of_conj s x0 d hs hd h1
        have h3 := GlobalTheory.PsCo.PcdConjLow.rM_of_mem_K x0 h2
        have h4 : δ ≤ rM ε (toM x0) := hx0.2
        linarith
    refine ⟨min 1 (rM ε (toM (x0⁻¹ * s * x0)) / 2), by positivity, fun x hx => ?_⟩
    by_contra hc
    push_neg at hc
    obtain ⟨y, hy, hyx⟩ := key x (hx.trans (min_le_left _ _)) hc
    have h1 : rM ε (toM (x0⁻¹ * s * x0)) ≤ rM ε (toM (y⁻¹ * s * y)) := hmin hy
    have h2 := min_le_right 1 (rM ε (toM (x0⁻¹ * s * x0)) / 2)
    linarith

end GlobalTheory.PsCo.Pcd

end
end
