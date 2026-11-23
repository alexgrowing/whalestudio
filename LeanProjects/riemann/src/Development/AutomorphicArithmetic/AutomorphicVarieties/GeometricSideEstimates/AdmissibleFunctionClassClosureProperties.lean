import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
open UpperTheory.V.Lit.Geo
open scoped ContDiff

section aux

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private def pA (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Subalgebra ℂ (V → ℂ) :=
  Algebra.adjoin ℂ (Set.range fun l : V →ₗ[ℝ] ℂ => (l : V → ℂ))

omit [FiniteDimensional ℝ V] in
private theorem lin_mem (l : V →ₗ[ℝ] ℂ) : (l : V → ℂ) ∈ pA V :=
  Algebra.subset_adjoin ⟨l, rfl⟩

omit [FiniteDimensional ℝ V] in
private theorem const_mem (c : ℂ) : (fun _ : V => c) ∈ pA V :=
  (pA V).algebraMap_mem c

private theorem pA_smooth {P : V → ℂ} (hP : P ∈ pA V) : ContDiff ℝ ∞ P := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    exact (LinearMap.toContinuousLinearMap l).contDiff
  | algebraMap c => exact contDiff_const (c := c)
  | add f g _ _ hf hg => exact hf.add hg
  | mul f g _ _ hf hg => exact hf.mul hg

omit [FiniteDimensional ℝ V] in
private theorem pA_comp (T : V →ₗ[ℝ] V) {P : V → ℂ} (hP : P ∈ pA V) : (fun x => P (T x)) ∈ pA V := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    exact lin_mem (l.comp T)
  | algebraMap c => exact const_mem c
  | add f g _ _ hf hg => exact (pA V).add_mem hf hg
  | mul f g _ _ hf hg => exact (pA V).mul_mem hf hg

private theorem pA_der (F : V → V) (hF : ∀ l : V →ₗ[ℝ] ℂ, (fun x => l (F x)) ∈ pA V) {P : V → ℂ}
    (hP : P ∈ pA V) : (fun x => fderiv ℝ P x (F x)) ∈ pA V := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    have h : (fun x => fderiv ℝ (l : V → ℂ) x (F x)) = fun x => l (F x) := by
      funext x
      have := (LinearMap.toContinuousLinearMap l).fderiv (x := x)
      exact congrArg (fun L : V →L[ℝ] ℂ => L (F x)) this
    exact h ▸ hF l
  | algebraMap c =>
    have h : (fun x => fderiv ℝ (algebraMap ℂ (V → ℂ) c) x (F x)) = fun _ => 0 := by
      funext x
      have : fderiv ℝ (algebraMap ℂ (V → ℂ) c) x = 0 := fderiv_const_apply c
      rw [this]; rfl
    rw [h]
    exact const_mem 0
  | add f g hf' hg' hf hg =>
    have df := (pA_smooth hf').differentiable (by simp)
    have dg := (pA_smooth hg').differentiable (by simp)
    have h : (fun x => fderiv ℝ (f + g) x (F x)) =
        (fun x => fderiv ℝ f x (F x)) + fun x => fderiv ℝ g x (F x) := by
      funext x
      rw [fderiv_add (df x) (dg x)]
      rfl
    rw [h]
    exact (pA V).add_mem hf hg
  | mul f g hf' hg' hf hg =>
    have df := (pA_smooth hf').differentiable (by simp)
    have dg := (pA_smooth hg').differentiable (by simp)
    have h : (fun x => fderiv ℝ (f * g) x (F x)) =
        f * (fun x => fderiv ℝ g x (F x)) + g * fun x => fderiv ℝ f x (F x) := by
      funext x
      rw [fderiv_mul (df x) (dg x)]
      simp
    rw [h]
    exact (pA V).add_mem ((pA V).mul_mem hf' hg) ((pA V).mul_mem hg' hf)

private theorem pA_bd (q : V → ℝ) (hq : ∀ x, ‖x‖ ^ 2 ≤ q x) {P : V → ℂ} (hP : P ∈ pA V) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x, ‖P x‖ ≤ C * (1 + q x) ^ k := by
  have h1 : ∀ x, 1 ≤ 1 + q x := fun x => by nlinarith [hq x, sq_nonneg ‖x‖]
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    refine ⟨‖LinearMap.toContinuousLinearMap l‖, 1, norm_nonneg _, fun x => ?_⟩
    refine ((LinearMap.toContinuousLinearMap l).le_opNorm x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [pow_one]
    nlinarith [hq x, sq_nonneg (‖x‖ - 1), sq_nonneg ‖x‖]
  | algebraMap c =>
    refine ⟨‖c‖, 0, norm_nonneg _, fun x => ?_⟩
    rw [pow_zero, mul_one]
    exact le_rfl
  | add f g _ _ hf hg =>
    obtain ⟨C, k, hC, hf⟩ := hf
    obtain ⟨D, m, hD, hg⟩ := hg
    refine ⟨C + D, k + m, add_nonneg hC hD, fun x => ?_⟩
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ((hf x).trans ?_) ((hg x).trans ?_)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (h1 x) (Nat.le_add_right _ _)) hC
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (h1 x) (Nat.le_add_left _ _)) hD
  | mul f g _ _ hf hg =>
    obtain ⟨C, k, hC, hf⟩ := hf
    obtain ⟨D, m, hD, hg⟩ := hg
    refine ⟨C * D, k + m, mul_nonneg hC hD, fun x => ?_⟩
    rw [Pi.mul_apply, norm_mul, pow_add, mul_mul_mul_comm]
    exact mul_le_mul (hf x) (hg x) (norm_nonneg _) ((norm_nonneg _).trans (hf x))

end aux

theorem UpperTheory.admissibleFunctionClass_closure_properties :
    PolyBd := by
  intro E _ _ a P hP
  have hq := fun x => ((UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.2.2 x).1
  refine ⟨pA_smooth hP, ?_, fun T => ⟨?_, pA_comp T hP, fun u => ?_⟩⟩
  · obtain ⟨C, k, _, h⟩ := pA_bd qf hq hP
    exact ⟨C, k, h⟩
  · exact pA_der T (fun l => lin_mem (l.comp T)) hP
  · exact pA_der (fun _ => u) (fun l => const_mem (l u)) hP
