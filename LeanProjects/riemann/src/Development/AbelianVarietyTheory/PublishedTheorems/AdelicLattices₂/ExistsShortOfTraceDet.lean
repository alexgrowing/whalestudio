import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MinkowskiLinearForms

namespace GlobalTheory.HermClass

open MeasureTheory Module Submodule NumberField Matrix

theorem exists_int_vecMul_lt {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) {t : ℝ} (ht : 0 < t) (h : |A.det| < t ^ Fintype.card ι) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ ∀ j, |∑ i, (z i : ℝ) * A i j| < t := by
  first
  | exact @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms
  | exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms
  | (apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)
  | (intros; apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms ..)

theorem det_ne_zero_and_abs_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℚ)
    {M : ℤ} (hM : M ≠ 0)
    (h : ∀ x : ι → ℚ, (∀ j, ∃ m : ℤ, (x ᵥ* T) j = m) → ∀ i, ∃ m : ℤ, M * x i = m) :
    T.det ≠ 0 ∧ |T.det| ≤ |(M : ℚ)| ^ Fintype.card ι := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have h0 : T.det ≠ 0 := by
    intro hd
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    have hi' : x i ≠ 0 := hi
    obtain ⟨m, hm⟩ := h ((2 * M * x i)⁻¹ • x) (fun j => ⟨0, by rw [Matrix.smul_vecMul, hx]; simp⟩) i
    have h2 : (2 * m : ℚ) = 1 := by
      rw [← hm]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega
  refine ⟨h0, ?_⟩
  have hu : IsUnit T.det := isUnit_iff_ne_zero.2 h0
  have hK : ∀ k i, ∃ m : ℤ, M * T⁻¹ k i = m := fun k => h (T⁻¹ k) fun j => by
    have : (T⁻¹ k ᵥ* T) j = (T⁻¹ * T) k j := rfl
    rw [this, Matrix.nonsing_inv_mul T hu, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  choose K hK using hK
  have hKe : (Int.castRingHom ℚ).mapMatrix (Matrix.of K) = (M : ℚ) • T⁻¹ := by
    ext k i; simp [← hK]
  have hdet : (((Matrix.of K).det : ℤ) : ℚ) * T.det = (M : ℚ) ^ Fintype.card ι := by
    have := (Int.castRingHom ℚ).map_det (Matrix.of K)
    rw [hKe, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at this
    rw [← eq_intCast (Int.castRingHom ℚ), this]; field_simp
  have hK0 : (Matrix.of K).det ≠ 0 := by
    intro hz; rw [hz] at hdet
    exact pow_ne_zero _ hM' (by simpa using hdet.symm)
  have h1 : (1 : ℚ) ≤ |(((Matrix.of K).det : ℤ) : ℚ)| := by exact_mod_cast Int.one_le_abs hK0
  rw [← abs_pow, ← hdet, abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) h1

theorem exists_short_of_trace_det {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : LinearMap.BilinForm F V) (hq : LinearMap.IsSymm q) {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : κ → V) (hκ : Fintype.card κ = finrank ℚ F * finrank F V) {t : ℝ} (ht : 0 < t)
    (h0 : (Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det ≠ 0)
    (h1 : |(((Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det : ℚ) : ℝ)| <
      (t ^ Fintype.card κ) ^ 2) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ ∀ φ : F →+* ℂ,
      ‖φ (q (∑ i, z i • b i) (∑ i, z i • b i))‖ ≤ finrank F V * t ^ 2 := by
  classical
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hq
  set ρ : (F →+* ℂ) → (F →+* ℝ) := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding
    with hρ
  have hρc : ∀ φ x, ((ρ φ x : ℝ) : ℂ) = φ x := fun φ x => by simp [hρ]
  have hqe : ∀ x y, q x y = ∑ k, e.repr x k * e.repr y k * q (e k) (e k) := by
    intro x y
    conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro l _ hl
      have : q (e l) (e k) = 0 := he hl
      rw [this, mul_zero]
    · simp
  have htr : ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, ρ φ x := by
    intro x
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)
    rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x) _ (fun _ => rfl)] at h
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, hρc, ← h]
    simp
  let ε : κ ≃ (F →+* ℂ) × Fin (finrank F V) := Fintype.equivOfCardEq (by
    rw [hκ, Fintype.card_prod, Embeddings.card, Fintype.card_fin])
  let a : κ → ℝ := fun j => ρ (ε j).1 (q (e (ε j).2) (e (ε j).2))
  let B : Matrix κ κ ℝ := Matrix.of fun i j => ρ (ε j).1 (e.repr (b i) (ε j).2)
  set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT
  have hTB : (Rat.castHom ℝ).mapMatrix T = B * Matrix.diagonal a * Bᵀ := by
    ext i i'
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply, hT, Matrix.of_apply,
      eq_ratCast, htr, Matrix.transpose_apply, B, a]
    rw [Fintype.sum_equiv ε _ (fun p => ρ p.1 (e.repr (b i) p.2) * ρ p.1 (q (e p.2) (e p.2)) *
      ρ p.1 (e.repr (b i') p.2)) (fun _ => rfl), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [hqe, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  have hdT : ((T.det : ℚ) : ℝ) = B.det ^ 2 * ∏ j, a j := by
    have := (Rat.castHom ℝ).map_det T
    rw [hTB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    rw [← eq_ratCast (Rat.castHom ℝ), this]; ring
  let A : Matrix κ κ ℝ := B * Matrix.diagonal fun j => Real.sqrt |a j|
  have hdA : A.det ^ 2 = |((T.det : ℚ) : ℝ)| := by
    rw [hdT, Matrix.det_mul, Matrix.det_diagonal, mul_pow, ← Finset.prod_pow, abs_mul,
      Finset.abs_prod, abs_of_nonneg (sq_nonneg B.det)]
    simp only [Real.sq_sqrt (abs_nonneg _)]
  have hA0 : A.det ≠ 0 := by
    intro hz
    rw [hz] at hdA
    apply h0
    have : ((T.det : ℚ) : ℝ) = 0 := by simpa using hdA.symm
    exact_mod_cast this
  have hA1 : |A.det| < t ^ Fintype.card κ := by
    apply abs_lt_of_sq_lt_sq _ (by positivity)
    rwa [hdA]
  obtain ⟨z, hz0, hz⟩ := exists_int_vecMul_lt A hA0 ht hA1
  refine ⟨z, hz0, fun φ => ?_⟩
  set v := ∑ i, z i • b i with hv
  rw [← hρc, Complex.norm_real, hqe, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k, ‖ρ φ (e.repr v k * e.repr v k * q (e k) (e k))‖ ≤ t ^ 2 := by
    intro k
    have h2 := hz (ε.symm (φ, k))
    have h3 : ∑ i, (z i : ℝ) * A i (ε.symm (φ, k)) =
        ρ φ (e.repr v k) * Real.sqrt |ρ φ (q (e k) (e k))| := by
      have hc : e.repr v k = ∑ i, (z i : F) * e.repr (b i) k := by
        rw [← e.coord_apply, hv, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, zsmul_eq_mul, e.coord_apply]
      rw [hc, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [A, Matrix.mul_diagonal, B, a, Matrix.of_apply, Equiv.apply_symm_apply,
        mul_assoc, map_mul, map_intCast]
    rw [h3] at h2
    have h4 := (sq_lt_sq' (abs_lt.1 h2).1 (abs_lt.1 h2).2).le
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)] at h4
    rw [map_mul, map_mul, Real.norm_eq_abs, abs_mul, abs_mul_self]
    rwa [sq] at h4
  calc _ ≤ ∑ _k : Fin (finrank F V), t ^ 2 := Finset.sum_le_sum fun k _ => this k
    _ = _ := by simp

end GlobalTheory.HermClass
