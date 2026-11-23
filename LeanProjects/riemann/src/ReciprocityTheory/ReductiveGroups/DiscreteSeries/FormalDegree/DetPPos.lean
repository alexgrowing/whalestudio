import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

namespace PolarJacobianDeterminant

variable {n : ℕ}

theorem det_pos_of_posForm {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : V →ₗ[ℝ] V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hBs : ∀ v w, B v w = B w v)
    (hB : ∀ v, v ≠ 0 → 0 < B v v) (hT : ∀ v w, B v (T w) = B (T v) w)
    (hTp : ∀ v, v ≠ 0 → 0 < B v (T v)) : 0 < LinearMap.det T := by
  by_contra hneg
  push_neg at hneg
  set f : ℝ → ℝ := fun t => LinearMap.det (t • T + (1 - t) • LinearMap.id) with hf
  have hcont : Continuous f := by
    let b := Module.finBasis ℝ V
    have e : f = fun t => (t • LinearMap.toMatrix b b T +
        (1 - t) • (1 : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ)).det := by
      funext t
      show LinearMap.det (t • T + (1 - t) • LinearMap.id) = _
      rw [← LinearMap.det_toMatrix b, map_add, map_smul, map_smul, LinearMap.toMatrix_id]
    rw [e]
    exact ((continuous_id.smul continuous_const).add
      ((continuous_const.sub continuous_id).smul continuous_const)).matrix_det
  have h1 : f 1 ≤ 0 := by simpa [hf] using hneg
  have h0 : 0 ≤ f 0 := by simp [hf]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn ⟨h1, h0⟩
  have hdet : LinearMap.det (t • T + (1 - t) • LinearMap.id) = 0 := hft
  obtain ⟨v, hvk, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.bot_lt_ker_of_det_eq_zero hdet).ne'
  have hSv : (t • T + (1 - t) • LinearMap.id : V →ₗ[ℝ] V) v = 0 := LinearMap.mem_ker.1 hvk
  have hE : B v ((t • T + (1 - t) • LinearMap.id : V →ₗ[ℝ] V) v) =
      t * B v (T v) + (1 - t) * B v v := by
    simp
  rw [hSv, map_zero] at hE
  have ha := hTp v hv0
  have hb := hB v hv0
  obtain ⟨ht0, ht1⟩ := ht
  rcases ht0.eq_or_lt with h | h
  · rw [← h] at hE
    linarith
  · have h2 : 0 < t * B v (T v) := mul_pos h ha
    have h3 : 0 ≤ (1 - t) * B v v := mul_nonneg (sub_nonneg.2 ht1) hb.le
    linarith

def trF (X Z : Matrix (Fin n) (Fin n) ℂ) : ℝ := (∑ a, ∑ b, star (X a b) * Z a b).re

theorem sum_star_mul_eq_trace (X Z : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, star (X a b) * Z a b = trace (Xᴴ * Z) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem trace_conj_mul_left (U S X : Matrix (Fin n) (Fin n) ℂ) :
    trace (Xᴴ * (U * S * Uᴴ)) = trace ((Uᴴ * X * U)ᴴ * S) := by
  calc trace (Xᴴ * (U * S * Uᴴ)) = trace ((Xᴴ * U * S) * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = trace (Uᴴ * (Xᴴ * U * S)) := Matrix.trace_mul_comm _ _
    _ = trace ((Uᴴ * X * U)ᴴ * S) := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem trace_conj_mul_right (U S Z : Matrix (Fin n) (Fin n) ℂ) :
    trace ((U * S * Uᴴ)ᴴ * Z) = trace (Sᴴ * (Uᴴ * Z * U)) := by
  calc trace ((U * S * Uᴴ)ᴴ * Z) = trace (U * (Sᴴ * Uᴴ * Z)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = trace ((Sᴴ * Uᴴ * Z) * U) := Matrix.trace_mul_comm _ _
    _ = trace (Sᴴ * (Uᴴ * Z * U)) := by simp only [Matrix.mul_assoc]

theorem shc_pos (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with hu | hu
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 hu) hu
    · exact div_pos (Real.sinh_pos_iff.2 hu) hu

theorem shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg (neg_ne_zero.2 h), if_neg h, Real.sinh_neg, neg_div_neg_eq]

section U
variable {ε : Fin n → Bool} (y : PCoord ε → ℂ)

abbrev Uy : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)

theorem Uy_star_mul : (Uy y)ᴴ * Uy y = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp (pmat_isHermitian y).eigenvectorUnitary.prop
  exact h
theorem Uy_mul_star : Uy y * (Uy y)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp (pmat_isHermitian y).eigenvectorUnitary.prop
  exact h

theorem shcAd_eq (W : Matrix (Fin n) (Fin n) ℂ) :
    shcAd y W = Uy y * Matrix.of (fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) *
      ((Uy y)ᴴ * W * Uy y) i j) * (Uy y)ᴴ := rfl

theorem trF_shcAd_right (X Z : Matrix (Fin n) (Fin n) ℂ) :
    trF X (shcAd y Z) = (∑ i, ∑ j, ((shc (pev y i - pev y j) : ℝ) : ℂ) *
      (star (((Uy y)ᴴ * X * Uy y) i j) * ((Uy y)ᴴ * Z * Uy y) i j)).re := by
  unfold trF
  rw [shcAd_eq, sum_star_mul_eq_trace, trace_conj_mul_left, ← sum_star_mul_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

theorem trF_shcAd_left (X Z : Matrix (Fin n) (Fin n) ℂ) :
    trF (shcAd y X) Z = (∑ i, ∑ j, ((shc (pev y i - pev y j) : ℝ) : ℂ) *
      (star (((Uy y)ᴴ * X * Uy y) i j) * ((Uy y)ᴴ * Z * Uy y) i j)).re := by
  have hs : ∀ r : ℝ, star (r : ℂ) = r := fun r => Complex.conj_ofReal r
  unfold trF
  rw [shcAd_eq, sum_star_mul_eq_trace, trace_conj_mul_right, ← sum_star_mul_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply, star_mul', hs]
  ring

theorem trF_shcAd_pos (X : Matrix (Fin n) (Fin n) ℂ) (hX : X ≠ 0) : 0 < trF X (shcAd y X) := by
  rw [trF_shcAd_right]
  set W := (Uy y)ᴴ * X * Uy y with hW
  have hW0 : W ≠ 0 := by
    intro h
    apply hX
    calc X = Uy y * W * (Uy y)ᴴ := by
          rw [hW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Uy_mul_star, Matrix.one_mul,
            Matrix.mul_assoc, Uy_mul_star, Matrix.mul_one]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨i0, j0, hij⟩ : ∃ i j, W i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hW0 (Matrix.ext fun i j => h i j)
  have hterm : ∀ i j, (((shc (pev y i - pev y j) : ℝ) : ℂ) * (star (W i j) * W i j)).re =
      shc (pev y i - pev y j) * Complex.normSq (W i j) := by
    intro i j
    have h : star (W i j) * W i j = ((Complex.normSq (W i j) : ℝ) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    rw [h, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [Complex.re_sum, hterm]
  apply Finset.sum_pos'
  · intro i _
    exact Finset.sum_nonneg fun j _ => mul_nonneg (shc_pos _).le (Complex.normSq_nonneg _)
  · refine ⟨i0, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (shc_pos _).le (Complex.normSq_nonneg _)
    · exact ⟨j0, Finset.mem_univ _, mul_pos (shc_pos _) (Complex.normSq_pos.2 hij)⟩

end U

theorem trF_add_left (X X' Z : Matrix (Fin n) (Fin n) ℂ) : trF (X + X') Z = trF X Z + trF X' Z := by
  simp only [trF, Matrix.add_apply, star_add, add_mul, Finset.sum_add_distrib, Complex.add_re]

theorem trF_add_right (X Z Z' : Matrix (Fin n) (Fin n) ℂ) : trF X (Z + Z') = trF X Z + trF X Z' := by
  simp only [trF, Matrix.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem trF_comm (X Z : Matrix (Fin n) (Fin n) ℂ) : trF X Z = trF Z X := by
  unfold trF
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e1 : ∀ w : ℂ, (star w).re = w.re := fun w => Complex.conj_re w
  have e2 : ∀ w : ℂ, (star w).im = -w.im := fun w => Complex.conj_im w
  rw [Complex.mul_re, Complex.mul_re, e1, e2, e1, e2]
  ring

theorem trF_smul_left (c : ℝ) (X Z : Matrix (Fin n) (Fin n) ℂ) : trF (c • X) Z = c * trF X Z := by
  unfold trF
  have hs : star (c : ℂ) = c := Complex.conj_ofReal c
  have e : ∀ a b, star ((c • X) a b) * Z a b = (c : ℂ) * (star (X a b) * Z a b) := by
    intro a b
    rw [Matrix.smul_apply, Complex.real_smul, star_mul', hs, mul_assoc]
  simp only [e, ← Finset.mul_sum, Complex.re_ofReal_mul]

theorem trF_smul_right (c : ℝ) (X Z : Matrix (Fin n) (Fin n) ℂ) : trF X (c • Z) = c * trF X Z := by
  unfold trF
  have e : ∀ a b, star (X a b) * (c • Z) a b = (c : ℂ) * (star (X a b) * Z a b) := by
    intro a b
    rw [Matrix.smul_apply, Complex.real_smul, mul_left_comm]
  simp only [e, ← Finset.mul_sum, Complex.re_ofReal_mul]

theorem trF_self_pos (X : Matrix (Fin n) (Fin n) ℂ) (hX : X ≠ 0) : 0 < trF X X := by
  unfold trF
  obtain ⟨i0, j0, hij⟩ : ∃ i j, X i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hX (Matrix.ext fun i j => h i j)
  have hterm : ∀ i j, (star (X i j) * X i j).re = Complex.normSq (X i j) := by
    intro i j
    have h : star (X i j) * X i j = ((Complex.normSq (X i j) : ℝ) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    rw [h, Complex.ofReal_re]
  simp only [Complex.re_sum, hterm]
  apply Finset.sum_pos'
  · intro i _
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  · refine ⟨i0, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro j _
      exact Complex.normSq_nonneg _
    · exact ⟨j0, Finset.mem_univ _, Complex.normSq_pos.2 hij⟩

section P
variable {ε : Fin n → Bool}

theorem pmat_add' (v w : PCoord ε → ℂ) : pmat (v + w) = pmat v + pmat w := by
  ext a b
  rw [Matrix.add_apply]
  simp only [pmat]
  split_ifs <;> simp [star_add]

theorem pmat_smul' (c : ℝ) (v : PCoord ε → ℂ) : pmat (c • v) = c • pmat v := by
  have hs : ∀ r : ℝ, star (r : ℂ) = r := fun r => Complex.conj_ofReal r
  ext a b
  rw [Matrix.smul_apply]
  simp only [pmat]
  split_ifs <;> simp [Complex.real_smul, star_mul', hs]

theorem pmat_apply_coord (v : PCoord ε → ℂ) (ab : PCoord ε) : pmat v ab.1.1 ab.1.2 = v ab := by
  obtain ⟨⟨a, b⟩, h⟩ := ab
  have h' : b < a ∧ ε a ≠ ε b := h
  simp only [pmat, dif_pos h']

theorem pmat_ne_zero (v : PCoord ε → ℂ) (hv : v ≠ 0) : pmat v ≠ 0 := by
  intro h
  apply hv
  funext ab
  have := pmat_apply_coord v ab
  rw [h] at this
  simpa using this.symm

theorem shcAd_add' (y : PCoord ε → ℂ) (W W' : Matrix (Fin n) (Fin n) ℂ) :
    shcAd y (W + W') = shcAd y W + shcAd y W' := by
  simp only [shcAd_eq]
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  congr 2
  ext i j
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_add, Matrix.add_mul, mul_add]

theorem shcAd_smul' (y : PCoord ε → ℂ) (c : ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    shcAd y (c • W) = c • shcAd y W := by
  simp only [shcAd_eq]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  congr 2
  ext i j
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.smul_mul, Matrix.mul_smul, Complex.real_smul]
  ring

def shcAdCL (y : PCoord ε → ℂ) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun w := fun ab => shcAd y (pmat w) ab.1.1 ab.1.2
  map_add' v w := by
    funext ab; simp only [pmat_add', shcAd_add', Matrix.add_apply, Pi.add_apply]
  map_smul' c v := by
    funext ab; simp only [pmat_smul', shcAd_smul', Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]

theorem pmat_shcAdCL (y w : PCoord ε → ℂ) : pmat (shcAdCL y w) = shcAd y (pmat w) := by
  have hs : ∀ r : ℝ, star (r : ℂ) = r := fun r => Complex.conj_ofReal r
  have hZ : (pmat w)ᴴ = pmat w := pmat_isHermitian w
  have hN : ((Uy y)ᴴ * pmat w * Uy y)ᴴ = (Uy y)ᴴ * pmat w * Uy y := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hZ,
      Matrix.mul_assoc]
  have hM : (Matrix.of fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) * ((Uy y)ᴴ * pmat w * Uy y) i j)ᴴ =
      Matrix.of fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) * ((Uy y)ᴴ * pmat w * Uy y) i j := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, star_mul', hs,
      ← Matrix.conjTranspose_apply, hN, show pev y j - pev y i = -(pev y i - pev y j) by ring, shc_neg]
  have hH : (shcAd y (pmat w))ᴴ = shcAd y (pmat w) := by
    rw [shcAd_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hM]
    exact (Matrix.mul_assoc _ _ _).symm
  set s : Fin n → ℂ := fun a => if ε a then 1 else -1 with hsd
  set J : Matrix (Fin n) (Fin n) ℂ := diagonal s with hJd
  have hJJ : J * J = 1 := by
    rw [hJd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [hsd]
    split_ifs <;> norm_num
  have hJZ : ∀ z : PCoord ε → ℂ, J * pmat z * J = -pmat z := by
    intro z
    ext a b
    simp only [hJd, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply]
    by_cases hab : ε a = ε b
    · have h0 : pmat z a b = 0 := by simp [pmat, hab]
      rw [h0]
      simp
    · have hss : s a * s b = -1 := by
        simp only [hsd]
        cases h1 : ε a <;> cases h2 : ε b <;> simp_all
      linear_combination (pmat z a b) * hss
  have hY : pmat y = Uy y * diagonal (fun i => ((pev y i : ℝ) : ℂ)) * (Uy y)ᴴ :=
    (pmat_isHermitian y).spectral_theorem
  set Λ : Fin n → ℂ := fun i => ((pev y i : ℝ) : ℂ) with hΛ
  set Q := (Uy y)ᴴ * J * Uy y with hQ
  have hUU := Uy_star_mul y
  have hUU' := Uy_mul_star y
  have hQQ : Q * Q = 1 := by
    rw [hQ]
    calc (Uy y)ᴴ * J * Uy y * ((Uy y)ᴴ * J * Uy y) = (Uy y)ᴴ * J * (Uy y * (Uy y)ᴴ) * J * Uy y := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU', Matrix.mul_one, Matrix.mul_assoc ((Uy y)ᴴ) J J, hJJ, Matrix.mul_one, hUU]
  have hQD : Q * diagonal Λ * Q = -diagonal Λ := by
    have hJY : J * pmat y * J = -pmat y := hJZ y
    rw [hY] at hJY
    calc Q * diagonal Λ * Q = (Uy y)ᴴ * (J * (Uy y * diagonal Λ * (Uy y)ᴴ) * J) * Uy y := by
          rw [hQ]
          simp only [Matrix.mul_assoc]
      _ = (Uy y)ᴴ * (-(Uy y * diagonal Λ * (Uy y)ᴴ)) * Uy y := by rw [hJY]
      _ = -diagonal Λ := by
          rw [Matrix.mul_neg, Matrix.neg_mul]
          refine congrArg Neg.neg ?_
          simp only [← Matrix.mul_assoc]
          rw [hUU, Matrix.one_mul, Matrix.mul_assoc, hUU, Matrix.mul_one]
  have hQDc : Q * diagonal Λ = -(diagonal Λ * Q) := by
    calc Q * diagonal Λ = Q * diagonal Λ * (Q * Q) := by rw [hQQ, Matrix.mul_one]
      _ = (Q * diagonal Λ * Q) * Q := by simp only [Matrix.mul_assoc]
      _ = -(diagonal Λ * Q) := by rw [hQD, Matrix.neg_mul]
  have hQent : ∀ i k, Q i k ≠ 0 → pev y k = -pev y i := by
    intro i k hik
    have h := congrFun (congrFun hQDc i) k
    rw [Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul] at h
    have h2 : Q i k * (Λ k + Λ i) = 0 := by linear_combination h
    have h3 : Λ k + Λ i = 0 := (mul_eq_zero.1 h2).resolve_left hik
    simp only [hΛ] at h3
    have h5 : pev y k + pev y i = 0 := by exact_mod_cast h3
    linarith
  have hshc : ∀ i j k l, Q i k ≠ 0 → Q l j ≠ 0 → shc (pev y k - pev y l) = shc (pev y i - pev y j) := by
    intro i j k l h1 h2
    have e1 := hQent i k h1
    have e2 := hQent l j h2
    rw [show pev y k - pev y l = -(pev y i - pev y j) by linarith, shc_neg]
  have hN' : Q * ((Uy y)ᴴ * pmat w * Uy y) * Q = -((Uy y)ᴴ * pmat w * Uy y) := by
    calc Q * ((Uy y)ᴴ * pmat w * Uy y) * Q
        = (Uy y)ᴴ * (J * ((Uy y * (Uy y)ᴴ) * pmat w * (Uy y * (Uy y)ᴴ)) * J) * Uy y := by
          rw [hQ]
          simp only [Matrix.mul_assoc]
      _ = (Uy y)ᴴ * (J * pmat w * J) * Uy y := by rw [hUU', Matrix.one_mul, Matrix.mul_one]
      _ = -((Uy y)ᴴ * pmat w * Uy y) := by rw [hJZ w, Matrix.mul_neg, Matrix.neg_mul]
  have hMQ : Q * (Matrix.of fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) * ((Uy y)ᴴ * pmat w * Uy y) i j) * Q =
      -(Matrix.of fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) * ((Uy y)ᴴ * pmat w * Uy y) i j) := by
    set N := (Uy y)ᴴ * pmat w * Uy y with hNd
    ext i j
    have hE := congrFun (congrFun hN' i) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply] at hE ⊢
    have key : ∀ l k, Q i k * (((shc (pev y k - pev y l) : ℝ) : ℂ) * N k l) * Q l j =
        ((shc (pev y i - pev y j) : ℝ) : ℂ) * (Q i k * N k l * Q l j) := by
      intro l k
      by_cases h1 : Q i k = 0
      · simp [h1]
      by_cases h2 : Q l j = 0
      · simp [h2]
      rw [hshc i j k l h1 h2]
      ring
    calc ∑ l, (∑ k, Q i k * (((shc (pev y k - pev y l) : ℝ) : ℂ) * N k l)) * Q l j
        = ∑ l, ∑ k, ((shc (pev y i - pev y j) : ℝ) : ℂ) * (Q i k * N k l * Q l j) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => key l k
      _ = ((shc (pev y i - pev y j) : ℝ) : ℂ) * ∑ l, (∑ k, Q i k * N k l) * Q l j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = -(((shc (pev y i - pev y j) : ℝ) : ℂ) * N i j) := by
          rw [hE]
          ring
  have hJW : J * shcAd y (pmat w) * J = -shcAd y (pmat w) := by
    rw [shcAd_eq]
    calc J * (Uy y * (Matrix.of fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) *
            ((Uy y)ᴴ * pmat w * Uy y) i j) * (Uy y)ᴴ) * J
        = Uy y * (Q * (Matrix.of fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) *
            ((Uy y)ᴴ * pmat w * Uy y) i j) * Q) * (Uy y)ᴴ := by
          rw [hQ]
          simp only [← Matrix.mul_assoc]
          rw [hUU', Matrix.one_mul]
          simp only [Matrix.mul_assoc]
          rw [hUU', Matrix.mul_one]
      _ = -(Uy y * (Matrix.of fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) *
            ((Uy y)ᴴ * pmat w * Uy y) i j) * (Uy y)ᴴ) := by
          rw [hMQ, Matrix.mul_neg, Matrix.neg_mul]
  have hzero : ∀ a b, ε a = ε b → shcAd y (pmat w) a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hJW a) b
    simp only [hJd, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply] at h
    have hss : s a * s b = 1 := by
      simp only [hsd, hab]
      split_ifs <;> norm_num
    linear_combination (1 / 2 : ℂ) * h - (1 / 2 : ℂ) * (shcAd y (pmat w) a b) * hss
  ext a b
  have hHab : star (shcAd y (pmat w) b a) = shcAd y (pmat w) a b := by
    have h := congrFun (congrFun hH a) b
    rwa [Matrix.conjTranspose_apply] at h
  show (if h : b < a ∧ ε a ≠ ε b then shcAdCL y w ⟨(a, b), h⟩
    else if h' : a < b ∧ ε b ≠ ε a then star (shcAdCL y w ⟨(b, a), h'⟩) else 0) = shcAd y (pmat w) a b
  split_ifs with h1 h2
  · rfl
  · exact hHab
  · symm
    apply hzero
    by_contra hne
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact h2 ⟨hlt, Ne.symm hne⟩
    · exact hne (by rw [heq])
    · exact h1 ⟨hgt, hne⟩

def Bp (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => trF (pmat v) (pmat w))
    (fun v v' w => by simp only [pmat_add', trF_add_left])
    (fun c v w => by simp only [pmat_smul', trF_smul_left, smul_eq_mul])
    (fun v w w' => by simp only [pmat_add', trF_add_right])
    (fun c v w => by simp only [pmat_smul', trF_smul_right, smul_eq_mul])

theorem det_shcAdCL_pos (y : PCoord ε → ℂ) : 0 < LinearMap.det (shcAdCL y) := by
  apply det_pos_of_posForm (shcAdCL y) (Bp ε)
  · intro v w
    simp only [Bp, LinearMap.mk₂_apply]
    exact trF_comm _ _
  · intro v hv
    simp only [Bp, LinearMap.mk₂_apply]
    exact trF_self_pos _ (pmat_ne_zero v hv)
  · intro v w
    simp only [Bp, LinearMap.mk₂_apply, pmat_shcAdCL]
    rw [trF_shcAd_right, trF_shcAd_left]
  · intro v hv
    simp only [Bp, LinearMap.mk₂_apply, pmat_shcAdCL]
    exact trF_shcAd_pos y _ (pmat_ne_zero v hv)

end P

end PolarJacobianDeterminant

end ReciprocityTheory.ChartRestriction.DS
