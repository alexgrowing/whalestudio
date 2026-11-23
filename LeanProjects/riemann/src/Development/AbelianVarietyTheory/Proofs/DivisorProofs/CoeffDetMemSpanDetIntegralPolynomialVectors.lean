import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.DetCoeff

theorem prod_monomial_eq {τ R ι : Type} [CommSemiring R] (s : Finset ι) (f : ι → τ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, ih, monomial_mul, Finset.sum_insert hj, Finset.prod_insert hj]

open Classical in
theorem coeff_det_eq {F τ : Type} [Field F] {d : ℕ} (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F))
    (s : Finset (τ →₀ ℕ)) (hs : ∀ i k, (P i k).support ⊆ s) (m : τ →₀ ℕ) :
    coeff m P.det = ∑ g ∈ Fintype.piFinset (fun _ : Fin d => s),
      if ∑ k, g k = m then (Matrix.of fun i k => coeff (g k) (P i k)).det else 0 := by
  classical
  have hP : ∀ i k, P i k = ∑ n ∈ s, monomial n (coeff n (P i k)) := by
    intro i k
    conv_lhs => rw [(P i k).as_sum]
    exact Finset.sum_subset (hs i k) (fun n _ hn => by simp [MvPolynomial.notMem_support_iff.mp hn])
  have hprod : ∀ σ : Equiv.Perm (Fin d), ∏ k, P (σ k) k = ∑ g ∈ Fintype.piFinset (fun _ : Fin d => s),
      monomial (∑ k, g k) (∏ k, coeff (g k) (P (σ k) k)) := by
    intro σ
    rw [Finset.prod_congr rfl (fun k _ => hP (σ k) k), Finset.prod_univ_sum]
    exact Finset.sum_congr rfl (fun g _ => prod_monomial_eq _ _ _)
  rw [Matrix.det_apply]
  simp_rw [hprod, Finset.smul_sum, coeff_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Matrix.det_apply]
  split_ifs with h
  · subst h
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Units.smul_def, coeff_smul, coeff_monomial, if_pos rfl]
    rfl
  · refine Finset.sum_eq_zero (fun σ _ => ?_)
    simp only [Units.smul_def, coeff_smul, coeff_monomial, if_neg h, smul_zero]

end GlobalTheory.DetCoeff

namespace GlobalTheory.DetCoeff

theorem coeff_det_mem_span_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V) (τ : Type) (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F)), (∀ k m, ∑ i, coeff m (P i k) • b i ∈ M) → ∀ m, coeff m P.det ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
  intro F V _ _ _ _ _ _ M d b τ P hP m
  classical
  have hs : ∀ i k, (P i k).support ⊆ Finset.univ.biUnion (fun ik : Fin d × Fin d => (P ik.1 ik.2).support) :=
    fun i k => Finset.subset_biUnion_of_mem (fun ik : Fin d × Fin d => (P ik.1 ik.2).support) (Finset.mem_univ (i, k))
  rw [coeff_det_eq P _ hs m]
  refine Submodule.sum_mem _ (fun g _ => ?_)
  split_ifs
  · apply Submodule.subset_span
    refine ⟨fun k => ∑ i, coeff (g k) (P i k) • b i, fun k => hP k (g k), ?_⟩
    rw [Module.Basis.det_apply]
    congr 1
    ext i k
    simp [Module.Basis.toMatrix_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  · exact Submodule.zero_mem _

end GlobalTheory.DetCoeff
