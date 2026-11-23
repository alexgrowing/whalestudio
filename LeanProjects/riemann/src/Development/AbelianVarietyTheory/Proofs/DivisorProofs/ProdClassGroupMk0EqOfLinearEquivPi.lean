import Mathlib
open scoped nonZeroDivisors

namespace GlobalTheory.DetClass

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def mat {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i)) (a : (i : ι) → I i) :
    Matrix ι ι R := fun j i => (φ (Pi.single i (a i)) j : R)

theorem det_mem {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a : (i : ι) → I i) : (mat φ a).det ∈ ∏ j, J j := by
  rw [Matrix.det_apply]
  refine Ideal.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  have h : ∏ i, (mat φ a) (σ i) i ∈ ∏ i, J (σ i) :=
    Ideal.prod_mem_prod fun i _ => (φ (Pi.single i (a i)) (σ i)).2
  rwa [Equiv.prod_comp σ J] at h

theorem det_swap {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a b : (i : ι) → I i) :
    (∏ i, (b i : R)) * (mat φ a).det = (∏ i, (a i : R)) * (mat φ b).det := by
  have key : mat φ a * Matrix.diagonal (fun i => (b i : R))
      = mat φ b * Matrix.diagonal (fun i => (a i : R)) := by
    ext j i
    simp only [Matrix.mul_diagonal, mat]
    have h1 : (b i : R) • (Pi.single i (a i) : (k : ι) → I k)
        = (a i : R) • (Pi.single i (b i) : (k : ι) → I k) := by
      funext k
      by_cases hk : k = i
      · subst hk
        apply Subtype.ext
        simp [mul_comm]
      · simp [Pi.single_eq_of_ne hk]
    have h2 := congrArg (fun x => ((φ x) j : R)) h1
    simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul] at h2
    rw [mul_comm, h2, mul_comm]
  have h := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at h
  rw [mul_comm, h, mul_comm]

open Pointwise in
theorem span_mul_le {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (b : (i : ι) → I i) :
    Ideal.span {(mat φ b).det} * ∏ i, I i ≤ Ideal.span {∏ i, (b i : R)} * ∏ j, J j := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  have hP : ∏ i, I i = Submodule.span R (∏ i, (I i : Set R)) := by
    rw [← Submodule.prod_span]
    simp only [Submodule.span_eq]
  rw [hP] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).mp hx
    have hs := det_swap φ (fun i => ⟨g i, hg (Finset.mem_univ i)⟩) b
    simp only at hs
    rw [mul_comm ((mat φ b).det), ← hs]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (det_mem φ _)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Ideal.add_mem _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r hx

theorem mat_mul {I J : ι → Ideal R} (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩) * mat φ.toLinearMap (fun i => ⟨c, hI i⟩)
      = Matrix.diagonal fun _ => c * c := by
  ext j k
  simp only [Matrix.mul_apply, mat, Matrix.diagonal_apply, LinearEquiv.coe_coe]
  set v := φ (Pi.single k ⟨c, hI k⟩) with hv
  have hsw : ∀ i, (v i : R) • (Pi.single i ⟨c, hJ i⟩ : (l : ι) → J l)
      = c • (Pi.single i (v i) : (l : ι) → J l) := by
    intro i
    funext l
    by_cases hl : l = i
    · subst hl
      apply Subtype.ext
      simp [mul_comm]
    · simp [Pi.single_eq_of_ne hl]
  have hsum : ∑ i, (v i : R) • (Pi.single i ⟨c, hJ i⟩ : (l : ι) → J l) = c • v := by
    simp_rw [hsw, ← Finset.smul_sum, Finset.univ_sum_single]
  have h := congrArg (fun x => ((φ.symm x) j : R)) hsum
  simp only [map_sum, map_smul, hv, LinearEquiv.symm_apply_apply, Finset.sum_apply,
    Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] at h
  simp_rw [mul_comm _ ((v _ : J _) : R)]
  rw [h]
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk]

theorem exists_span_mul_eq [IsDomain R] {I J : ι → Ideal R}
    (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hc0 : c ≠ 0) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    ∃ x y : R, x ≠ 0 ∧ y ≠ 0 ∧ Ideal.span {x} * ∏ i, I i = Ideal.span {y} * ∏ i, J i := by
  set d : R := ∏ _i : ι, c with hd
  have h1 := span_mul_le φ.toLinearMap (fun i => ⟨c, hI i⟩)
  have h2 := span_mul_le φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩)
  simp only at h1 h2
  rw [← hd] at h1 h2
  set x := (mat φ.toLinearMap (fun i => ⟨c, hI i⟩)).det
  set y := (mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩)).det
  have hyx : y * x = d * d := by
    have h := congrArg Matrix.det (mat_mul φ c hI hJ)
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_mul_distrib] at h
    exact h
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ _ => hc0
  have hdd : d * d ≠ 0 := mul_ne_zero hd0 hd0
  have hy0 : y ≠ 0 := fun h => hdd (by rw [← hyx, h, zero_mul])
  refine ⟨d * d, d * y, hdd, mul_ne_zero hd0 hy0, le_antisymm ?_ ?_⟩
  · rw [← hyx, ← Ideal.span_singleton_mul_span_singleton, mul_assoc,
      ← Ideal.span_singleton_mul_span_singleton, mul_comm (Ideal.span {d}), mul_assoc]
    exact Ideal.mul_mono_right h1
  · rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc,
      ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
    exact Ideal.mul_mono_right h2

end GlobalTheory.DetClass

open GlobalTheory.DetClass in

theorem GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv (R : Type) [CommRing R] [IsDedekindDomain R]
    (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰)
    (h : Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R)))) :
    ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by
  classical
  obtain ⟨φ⟩ := h
  have hne : ∀ K : (Ideal R)⁰, ∃ e : R, e ∈ (K : Ideal R) ∧ e ≠ 0 := fun K =>
    Submodule.exists_mem_ne_zero_of_ne_bot (nonZeroDivisors.coe_ne_zero K)
  choose e he he0 using hne
  set c : R := (∏ i, e (I i)) * ∏ i, e (J i) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => he0 _)
    (Finset.prod_ne_zero_iff.mpr fun i _ => he0 _)
  have hI : ∀ i, c ∈ (I i : Ideal R) := fun i =>
    Ideal.mul_mem_right _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (he _))
  have hJ : ∀ i, c ∈ (J i : Ideal R) := fun i =>
    Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (he _))
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_span_mul_eq φ c hc0 hI hJ
  rw [← map_prod, ← map_prod, ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa only [Submonoid.coe_finsetProd] using hxy
