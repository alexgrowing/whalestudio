import Mathlib
import GroundTheory.AutomorphicForms.HilbertSchmidt

namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap

noncomputable section

theorem ennreal_two_mul_le_sq_add_sq (a b : ℝ≥0∞) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  rcases eq_or_ne b ∞ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Abs

theorem isSelfAdjoint_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : IsSelfAdjoint A :=
  ((nonneg_iff_isPositive A).1 hA).isSelfAdjoint

theorem adjoint_eq_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : A† = A :=
  (isSelfAdjoint_of_nonneg hA).adjoint_eq

theorem inner_apply_eq_norm_sqrt_sq {A : H →L[ℂ] H} (hA : 0 ≤ A) (x : H) :
    ⟪x, A x⟫_ℂ = ((‖CFC.sqrt A x‖ ^ 2 : ℝ) : ℂ) := by
  have hs : (CFC.sqrt A)† = CFC.sqrt A := adjoint_eq_of_nonneg (CFC.sqrt_nonneg A)
  have hA' : A = CFC.sqrt A * CFC.sqrt A := (CFC.sqrt_mul_sqrt_self A hA).symm
  conv_lhs => rw [hA', mul_def, comp_apply, ← hs, adjoint_inner_right, hs]
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem norm_abs_apply (T : H →L[ℂ] H) (x : H) : ‖CFC.abs T x‖ = ‖T x‖ := by
  have hR : (CFC.abs T)† = CFC.abs T := adjoint_eq_of_nonneg (CFC.abs_nonneg T)
  have h : ‖CFC.abs T x‖ ^ 2 = ‖T x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
    congr 1
    conv_lhs => rw [← adjoint_inner_right (CFC.abs T), hR, ← comp_apply, ← mul_def,
      CFC.abs_mul_abs, star_eq_adjoint, mul_def, comp_apply, adjoint_inner_right]
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

theorem exists_polar (T : H →L[ℂ] H) :
    ∃ V : H →L[ℂ] H, ‖V‖ ≤ 1 ∧ V.comp (CFC.abs T) = T ∧ (V†).comp T = CFC.abs T := by
  set R := CFC.abs T with hRdef
  set M : Submodule ℂ H := (LinearMap.range R.toLinearMap).topologicalClosure with hM
  have : CompleteSpace M := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let e : H →ₗ[ℂ] M := R.toLinearMap.codRestrict M
    (fun x => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))
  have he : ∀ x, (e x : H) = R x := fun x => rfl
  have hdense : DenseRange e := by
    rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
    intro y hy
    change y ∈ ((LinearMap.range R.toLinearMap).topologicalClosure : Set H) at hy
    rw [Submodule.topologicalClosure_coe, LinearMap.coe_range] at hy
    exact hy
  have hnorm : ∀ x, ‖T.toLinearMap x‖ ≤ 1 * ‖e x‖ := by
    intro x
    rw [one_mul, Submodule.coe_norm, he, norm_abs_apply]
    rfl
  let W : M →L[ℂ] H := T.toLinearMap.extendOfNorm e
  have hW : ∀ x, W (e x) = T x := fun x => LinearMap.extendOfNorm_eq hdense ⟨1, hnorm⟩ x
  have hWiso : ∀ m, ‖W m‖ = ‖m‖ := by
    intro m
    refine hdense.induction_on m (isClosed_eq W.continuous.norm continuous_norm) fun x => ?_
    rw [hW, Submodule.coe_norm, he, norm_abs_apply]
  let Wi : M →ₗᵢ[ℂ] H := { W.toLinearMap with norm_map' := hWiso }
  have hWinner : ∀ m m' : M, ⟪W m, W m'⟫_ℂ = ⟪m, m'⟫_ℂ := fun m m' => Wi.inner_map_map m m'
  refine ⟨W.comp M.orthogonalProjectionOnto, ?_, ?_, ?_⟩
  · refine (opNorm_comp_le _ _).trans ?_
    have h1 : ‖W‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun m => by rw [hWiso, one_mul]
    calc ‖W‖ * ‖M.orthogonalProjectionOnto‖ ≤ 1 * 1 := by
          gcongr
          exact Submodule.orthogonalProjectionOnto_norm_le M
      _ = 1 := one_mul 1
  · ext x
    show W (M.orthogonalProjectionOnto ((e x : M) : H)) = T x
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, hW]
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [comp_apply, adjoint_inner_left, comp_apply, ← hW x, hWinner,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, he]

end Abs

section TraceNorm

def traceNorm (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re
    ⟪stdHilbertBasis ℂ H i, CFC.abs T (stdHilbertBasis ℂ H i)⟫_ℂ)

theorem ofReal_re_inner_abs (T : H →L[ℂ] H) (x : H) :
    ENNReal.ofReal (RCLike.re ⟪x, CFC.abs T x⟫_ℂ) = ‖CFC.sqrt (CFC.abs T) x‖ₑ ^ 2 := by
  rw [inner_apply_eq_norm_sqrt_sq (CFC.abs_nonneg T), RCLike.re_to_complex, Complex.ofReal_re,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem traceNorm_eq_hsNormSq (T : H →L[ℂ] H) :
    traceNorm T = hsNormSq (CFC.sqrt (CFC.abs T)) := by
  simp only [traceNorm, ofReal_re_inner_abs]
  rfl

theorem traceNorm_eq_tsum {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    traceNorm T = ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, CFC.abs T (b i)⟫_ℂ) := by
  simp only [traceNorm_eq_hsNormSq, ofReal_re_inner_abs, hsNormSq_eq_tsum b]

def IsTraceClass (T : H →L[ℂ] H) : Prop := traceNorm T < ∞

theorem isTraceClass_iff_isHilbertSchmidt_sqrt (T : H →L[ℂ] H) :
    IsTraceClass T ↔ IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) := by
  rw [IsTraceClass, traceNorm_eq_hsNormSq, IsHilbertSchmidt]

theorem traceNorm_le_of_adjoint_comp {ι : Type*} (b : HilbertBasis ι ℂ H) {T V : H →L[ℂ] H}
    (hV : (V†).comp T = CFC.abs T) : traceNorm T ≤ ∑' i, ‖⟪V (b i), T (b i)⟫_ℂ‖ₑ := by
  rw [traceNorm_eq_tsum b]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← hV, comp_apply, adjoint_inner_right, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)

theorem enorm_le_one_of_norm_le_one {A : H →L[ℂ] H} (hA : ‖A‖ ≤ 1) : ‖A‖ₑ ≤ 1 := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hA

theorem tsum_enorm_inner_le_traceNorm {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    {U W : H →L[ℂ] H} (hU : ‖U‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ traceNorm T := by
  obtain ⟨V, hV1, hVT, -⟩ := exists_polar T
  set s := CFC.sqrt (CFC.abs T) with hsdef
  have hs : s† = s := adjoint_eq_of_nonneg (CFC.sqrt_nonneg _)
  have hss : s.comp s = CFC.abs T := CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
  have hpt : ∀ x y, ⟪U x, T (W y)⟫_ℂ = ⟪s ((V†) (U x)), s (W y)⟫_ℂ := by
    intro x y
    conv_lhs => rw [← hVT, ← hss, comp_apply, comp_apply, ← adjoint_inner_left V,
      ← hs, adjoint_inner_right, hs]
  have hVU : ‖(V†).comp U‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans ?_
    rw [adjoint.norm_map]
    calc ‖V‖ * ‖U‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have key : 2 * ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ 2 * traceNorm T := by
    calc 2 * ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ
        ≤ ∑' i, (‖s ((V†) (U (b i)))‖ₑ ^ 2 + ‖s (W (b i))‖ₑ ^ 2) := by
          rw [← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [hpt]
          calc 2 * ‖⟪s ((V†) (U (b i))), s (W (b i))⟫_ℂ‖ₑ
              ≤ 2 * (‖s ((V†) (U (b i)))‖ₑ * ‖s (W (b i))‖ₑ) := by
                gcongr; exact enorm_inner_le _ _
            _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
      _ = hsNormSq (s.comp ((V†).comp U)) + hsNormSq (s.comp W) := by
          rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
          rfl
      _ ≤ ‖(V†).comp U‖ₑ ^ 2 * hsNormSq s + ‖W‖ₑ ^ 2 * hsNormSq s :=
          add_le_add (hsNormSq_comp_right_le _ _) (hsNormSq_comp_right_le _ _)
      _ ≤ 1 ^ 2 * hsNormSq s + 1 ^ 2 * hsNormSq s := by
          gcongr
          · exact enorm_le_one_of_norm_le_one hVU
          · exact enorm_le_one_of_norm_le_one hW
      _ = 2 * traceNorm T := by rw [traceNorm_eq_hsNormSq, one_pow, one_mul, two_mul]
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 key

end TraceNorm

section Ideal

theorem norm_id_le_one : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1 := norm_id_le

theorem tsum_enorm_inner_le {ι : Type*} (b : HilbertBasis ι ℂ H) (T U W : H →L[ℂ] H) :
    ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ ‖U‖ₑ * ‖W‖ₑ * traceNorm T := by
  rcases eq_or_ne U 0 with rfl | hU
  · simp
  rcases eq_or_ne W 0 with rfl | hW
  · simp
  have hu : 0 < ‖U‖ := norm_pos_iff.2 hU
  have hw : 0 < ‖W‖ := norm_pos_iff.2 hW
  set U₀ : H →L[ℂ] H := ((‖U‖⁻¹ : ℝ) : ℂ) • U with hU₀def
  set W₀ : H →L[ℂ] H := ((‖W‖⁻¹ : ℝ) : ℂ) • W with hW₀def
  have hU₀ : ‖U₀‖ ≤ 1 := by
    rw [hU₀def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hu.ne']
  have hW₀ : ‖W₀‖ ≤ 1 := by
    rw [hW₀def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hw.ne']
  have hUx : ∀ x, U x = ((‖U‖ : ℝ) : ℂ) • U₀ x := fun x => by
    rw [hU₀def, smul_apply, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hu.ne',
      Complex.ofReal_one, one_smul]
  have hWx : ∀ x, W x = ((‖W‖ : ℝ) : ℂ) • W₀ x := fun x => by
    rw [hW₀def, smul_apply, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne',
      Complex.ofReal_one, one_smul]
  have hpt : ∀ i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ =
      ‖U‖ₑ * ‖W‖ₑ * ‖⟪U₀ (b i), T (W₀ (b i))⟫_ℂ‖ₑ := by
    intro i
    have h : ⟪U (b i), T (W (b i))⟫_ℂ =
        ((‖U‖ * ‖W‖ : ℝ) : ℂ) * ⟪U₀ (b i), T (W₀ (b i))⟫_ℂ := by
      rw [hUx, hWx, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
        Complex.ofReal_mul, mul_assoc]
    rw [h, enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  simp_rw [hpt, ENNReal.tsum_mul_left]
  gcongr
  exact tsum_enorm_inner_le_traceNorm b T hU₀ hW₀

theorem traceNorm_zero : traceNorm (0 : H →L[ℂ] H) = 0 := by
  simp [traceNorm]

theorem traceNorm_add_le (S T : H →L[ℂ] H) : traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (S + T)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc traceNorm (S + T) ≤ ∑' i, ‖⟪V (b i), (S + T) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖⟪V (b i), S (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ +
          ‖⟪V (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [add_apply, inner_add_right, id_apply]
        exact enorm_add_le _ _
    _ = _ := ENNReal.tsum_add
    _ ≤ ‖V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm S +
          ‖V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T :=
        add_le_add (tsum_enorm_inner_le b S _ _) (tsum_enorm_inner_le b T _ _)
    _ ≤ 1 * 1 * traceNorm S + 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm S + traceNorm T := by simp only [one_mul]

theorem traceNorm_comp_left_le (C T : H →L[ℂ] H) : traceNorm (C.comp T) ≤ ‖C‖ₑ * traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (C.comp T)
  let b := stdHilbertBasis ℂ H
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  have hCV : ‖(C†).comp V‖ₑ ≤ ‖C‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((opNorm_comp_le _ _).trans ?_)
    rw [adjoint.norm_map]
    calc ‖C‖ * ‖V‖ ≤ ‖C‖ * 1 := by gcongr
      _ = ‖C‖ := mul_one _
  calc traceNorm (C.comp T) ≤ ∑' i, ‖⟪V (b i), (C.comp T) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪((C†).comp V) (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ := by
        congr 1; ext i
        rw [comp_apply, comp_apply, adjoint_inner_left, id_apply]
    _ ≤ ‖(C†).comp V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ ‖C‖ₑ * 1 * traceNorm T := by gcongr
    _ = ‖C‖ₑ * traceNorm T := by rw [mul_one]

theorem traceNorm_comp_right_le (T C : H →L[ℂ] H) :
    traceNorm (T.comp C) ≤ ‖C‖ₑ * traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (T.comp C)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc traceNorm (T.comp C) ≤ ∑' i, ‖⟪V (b i), (T.comp C) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪V (b i), T (C (b i))⟫_ℂ‖ₑ := rfl
    _ ≤ ‖V‖ₑ * ‖C‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ 1 * ‖C‖ₑ * traceNorm T := by gcongr
    _ = ‖C‖ₑ * traceNorm T := by rw [one_mul]

theorem traceNorm_adjoint_le (T : H →L[ℂ] H) : traceNorm (T†) ≤ traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (T†)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc traceNorm (T†) ≤ ∑' i, ‖⟪V (b i), (T†) (b i)⟫_ℂ‖ₑ := traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪ContinuousLinearMap.id ℂ H (b i), T (V (b i))⟫_ℂ‖ₑ := by
        congr 1; ext i
        rw [adjoint_inner_right, enorm_inner_comm, id_apply]
    _ ≤ ‖ContinuousLinearMap.id ℂ H‖ₑ * ‖V‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm T := by simp only [one_mul]

theorem traceNorm_adjoint (T : H →L[ℂ] H) : traceNorm (T†) = traceNorm T :=
  le_antisymm (traceNorm_adjoint_le T) (by simpa using traceNorm_adjoint_le (T†))

theorem traceNorm_smul_le (c : ℂ) (T : H →L[ℂ] H) : traceNorm (c • T) ≤ ‖c‖ₑ * traceNorm T := by
  have h : c • T = (c • ContinuousLinearMap.id ℂ H).comp T := by ext x; simp
  rw [h]
  refine (traceNorm_comp_left_le _ _).trans ?_
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((norm_smul_le _ _).trans ?_)
  calc ‖c‖ * ‖ContinuousLinearMap.id ℂ H‖ ≤ ‖c‖ * 1 := by gcongr; exact norm_id_le_one
    _ = ‖c‖ := mul_one _

theorem isTraceClass_iff (T : H →L[ℂ] H) : IsTraceClass T ↔ traceNorm T < ∞ := Iff.rfl

theorem IsTraceClass.add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) :=
  (traceNorm_add_le S T).trans_lt (ENNReal.add_lt_top.2 ⟨hS, hT⟩)

theorem IsTraceClass.smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    IsTraceClass (c • T) :=
  (traceNorm_smul_le c T).trans_lt (ENNReal.mul_lt_top (by simp) hT)

theorem IsTraceClass.comp_left {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    IsTraceClass (C.comp T) :=
  (traceNorm_comp_left_le C T).trans_lt (ENNReal.mul_lt_top (by simp) hT)

theorem IsTraceClass.comp_right {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    IsTraceClass (T.comp C) :=
  (traceNorm_comp_right_le T C).trans_lt (ENNReal.mul_lt_top (by simp) hT)

theorem IsTraceClass.adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) : IsTraceClass (T†) := by
  rw [IsTraceClass, traceNorm_adjoint]; exact hT

variable (H) in

def traceClass : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | IsTraceClass T}
  add_mem' hS hT := hS.add hT
  zero_mem' := by
    show traceNorm (0 : H →L[ℂ] H) < ∞
    rw [traceNorm_zero]; exact ENNReal.zero_lt_top
  smul_mem' c _ hT := hT.smul c

theorem two_mul_traceNorm_comp_le (A B : H →L[ℂ] H) :
    2 * traceNorm (A.comp B) ≤ hsNormSq A + hsNormSq B := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (A.comp B)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc 2 * traceNorm (A.comp B) ≤ 2 * ∑' i, ‖⟪V (b i), A (B (b i))⟫_ℂ‖ₑ := by
        gcongr; exact traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖((A†).comp V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← adjoint_inner_left, ← comp_apply (A†) V]
        calc 2 * ‖⟪((A†).comp V) (b i), B (b i)⟫_ℂ‖ₑ
            ≤ 2 * (‖((A†).comp V) (b i)‖ₑ * ‖B (b i)‖ₑ) := by gcongr; exact enorm_inner_le _ _
          _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
    _ = hsNormSq ((A†).comp V) + hsNormSq B := by
        rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
    _ ≤ ‖V‖ₑ ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr; exact hsNormSq_comp_right_le _ _
    _ ≤ 1 ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr
    _ = hsNormSq A + hsNormSq B := by rw [one_pow, one_mul, hsNormSq_adjoint]

theorem isTraceClass_comp {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsTraceClass (A.comp B) := by
  have h := (two_mul_traceNorm_comp_le A B).trans_lt (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  rw [IsTraceClass]
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.mul_top two_ne_zero] at h
  exact lt_irrefl _ h

theorem IsTraceClass.exists_comp {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H, IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ T = A.comp B := by
  obtain ⟨V, -, hVT, -⟩ := exists_polar T
  have hs : IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) :=
    (isTraceClass_iff_isHilbertSchmidt_sqrt T).1 hT
  refine ⟨V.comp (CFC.sqrt (CFC.abs T)), CFC.sqrt (CFC.abs T), hs.comp_left V, hs, ?_⟩
  have hss : (CFC.sqrt (CFC.abs T)).comp (CFC.sqrt (CFC.abs T)) = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
  rw [comp_assoc, hss, hVT]

end Ideal

section Trace

def trace (T : H →L[ℂ] H) : ℂ :=
  ∑' i, ⟪stdHilbertBasis ℂ H i, T (stdHilbertBasis ℂ H i)⟫_ℂ

theorem trace_comp_comm_of_isHilbertSchmidt {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : trace (A.comp B) = trace (B.comp A) :=
  (hasSum_inner_comp_comm (stdHilbertBasis ℂ H) (stdHilbertBasis ℂ H) hA hB).tsum_eq

theorem IsTraceClass.hasSum_trace {T : H →L[ℂ] H} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι ℂ H) : HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (trace T) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  have h1 := hasSum_inner_comp_comm b (stdHilbertBasis ℂ H) hA hB
  rw [trace_comp_comm_of_isHilbertSchmidt hA hB]
  exact h1

theorem tsum_enorm_inner_self_le {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ ≤ traceNorm T := by
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ
      = ∑' i, ‖⟪ContinuousLinearMap.id ℂ H (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ :=
        rfl
    _ ≤ ‖ContinuousLinearMap.id ℂ H‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T :=
        tsum_enorm_inner_le b T _ _
    _ ≤ 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm T := by simp only [one_mul]

theorem IsTraceClass.summable_norm_inner {T : H →L[ℂ] H} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι ℂ H) : Summable fun i => ‖⟪b i, T (b i)⟫_ℂ‖ := by
  have h := ENNReal.summable_toReal ((tsum_enorm_inner_self_le b T).trans_lt hT).ne
  simpa using h

theorem enorm_trace_le (T : H →L[ℂ] H) : ‖trace T‖ₑ ≤ traceNorm T := by
  by_cases hT : IsTraceClass T
  · let b := stdHilbertBasis ℂ H
    have hs := hT.summable_norm_inner b
    calc ‖trace T‖ₑ = ENNReal.ofReal ‖trace T‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∑' i, ‖⟪b i, T (b i)⟫_ℂ‖) :=
          ENNReal.ofReal_le_ofReal ((hT.hasSum_trace b).norm_le_of_bounded hs.hasSum fun _ => le_rfl)
      _ = ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
          simp only [ofReal_norm]
      _ ≤ traceNorm T := tsum_enorm_inner_self_le b T
  · rw [IsTraceClass, not_lt, top_le_iff] at hT
    rw [hT]; exact le_top

theorem trace_add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S + T) = trace S + trace T := by
  let b := stdHilbertBasis ℂ H
  refine ((hS.add hT).hasSum_trace b).unique ?_
  convert (hS.hasSum_trace b).add (hT.hasSum_trace b) using 1
  ext i
  rw [add_apply, inner_add_right]

theorem trace_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace (c • T) = c * trace T := by
  let b := stdHilbertBasis ℂ H
  refine ((hT.smul c).hasSum_trace b).unique ?_
  have hfun : (fun i => ⟪b i, (c • T) (b i)⟫_ℂ) = fun i => c * ⟪b i, T (b i)⟫_ℂ := by
    ext i; rw [smul_apply, inner_smul_right]
  rw [hfun]
  exact (hT.hasSum_trace b).mul_left c

theorem trace_comp_comm {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    trace (C.comp T) = trace (T.comp C) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  calc trace (C.comp (A.comp B)) = trace ((C.comp A).comp B) := by rw [comp_assoc]
    _ = trace (B.comp (C.comp A)) := trace_comp_comm_of_isHilbertSchmidt (hA.comp_left C) hB
    _ = trace ((B.comp C).comp A) := by rw [comp_assoc]
    _ = trace (A.comp (B.comp C)) := trace_comp_comm_of_isHilbertSchmidt (hB.comp_right C) hA
    _ = trace ((A.comp B).comp C) := by rw [comp_assoc]

theorem trace_adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace (T†) = starRingEnd ℂ (trace T) := by
  let b := stdHilbertBasis ℂ H
  refine (hT.adjoint.hasSum_trace b).unique ?_
  have hfun : (fun i => ⟪b i, (T†) (b i)⟫_ℂ) = fun i => star ⟪b i, T (b i)⟫_ℂ := by
    ext i; rw [adjoint_inner_right, ← inner_conj_symm]; rfl
  rw [hfun, starRingEnd_apply]
  exact (hT.hasSum_trace b).star

end Trace

end

end GroundTheory.Automorphic
