import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CrRowActRowAct

noncomputable section

namespace PI.WSF

open MvPolynomial MeasureTheory Matrix

private theorem entry_le_lemma {N : ℕ} {x : Matrix (Fin N) (Fin N) ℂ} (hx : x ∈ unitaryGroup (Fin N) ℂ)
    (i j : Fin N) : ‖x i j‖ ≤ 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hx) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h3 : (∑ k, Complex.normSq (x i k) : ℝ) = 1 := by
    have h4 : ((∑ k, Complex.normSq (x i k) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← h]
      exact Finset.sum_congr rfl fun k _ => (Complex.mul_conj (x i k)).symm
    exact_mod_cast h4
  have h5 : Complex.normSq (x i j) ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (x i k)) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at h5
  nlinarith [norm_nonneg (x i j)]

theorem ci_compact (N : ℕ) : IsCompact (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hset : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) = {x | x * star x = 1} := by
    ext x
    exact Matrix.mem_unitaryGroup_iff
  have hclosed : IsClosed (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
    rw [hset]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  have hbound : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    intro x hx
    exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
      mem_closedBall_zero_iff.mpr (entry_le_lemma hx i j)
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset
    hclosed hbound

theorem ci_cont {N : ℕ} (p : MvPolynomial (Fin N × Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => evalM x p := by
  unfold evalM
  exact (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun v => (continuous_apply v.2).comp (continuous_apply v.1))

theorem ci_cont2 {N : ℕ} (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => evalM x p * star (evalM x q) :=
  (ci_cont p).mul (ci_cont q).star

theorem ci_integrable {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    {f : Matrix (Fin N) (Fin N) ℂ → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨hprob, hae, -, -⟩ := hμ
  have h := hf.continuousOn.integrableOn_compact (μ := μ) (ci_compact N)
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h
  exact h

theorem ci_evalM_add {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (p + q) = evalM x p + evalM x q := by
  simp [evalM]

theorem ci_evalM_smul {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (c • p) = c * evalM x p := by
  simp [evalM]

def Aform {N : ℕ} (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) (p q : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  ∫ x, evalM x p * star (evalM x q) ∂μ

def Alin {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (q : MvPolynomial (Fin N × Fin N) ℂ) : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun p := Aform μ p q
  map_add' p p' := by
    unfold Aform
    rw [← integral_add (ci_integrable hμ (ci_cont2 p q)) (ci_integrable hμ (ci_cont2 p' q))]
    congr 1
    funext x
    rw [ci_evalM_add]
    ring
  map_smul' c p := by
    unfold Aform
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    rw [ci_evalM_smul]
    ring

theorem ci_Alin_apply {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) : Alin hμ q p = Aform μ p q := rfl

theorem ci_herm {N : ℕ} (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ q p = star (Aform μ p q) := by
  unfold Aform
  have h := integral_conj (μ := μ) (f := fun x => evalM x p * star (evalM x q))
  rw [show star (∫ x, evalM x p * star (evalM x q) ∂μ) =
    (starRingEnd ℂ) (∫ x, evalM x p * star (evalM x q) ∂μ) from rfl, ← h]
  congr 1
  funext x
  simp [mul_comm]

private theorem evalM_rowAct {N : ℕ} (u x : Matrix (Fin N) (Fin N) ℂ)
    (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ u p) = evalM (u * x) p := by
  induction p using MvPolynomial.induction_on
  next a =>
    simp [evalM, Formalism.GradedWeylDivisibility.rowAct]
  next p q hp hq =>
    rw [map_add, ci_evalM_add, ci_evalM_add, hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem ci_invariant {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (u : Matrix (Fin N) (Fin N) ℂ) (hu : u ∈ unitaryGroup (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ (Formalism.GradedWeylDivisibility.rowAct ℂ u p) (Formalism.GradedWeylDivisibility.rowAct ℂ u q) = Aform μ p q := by
  obtain ⟨-, -, -, hL⟩ := hμ
  unfold Aform
  simp only [evalM_rowAct]
  exact hL u hu (fun x => evalM x p * star (evalM x q)) (ci_cont2 p q)

end PI.WSF
