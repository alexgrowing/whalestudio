import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace PositivityTheory.Xgp.poly_towt_bound

theorem abs_coeff_le {σ : Type} (P : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |coeff m P| ≤ ∑ d ∈ P.support, |coeff d P| := by
  by_cases h : m ∈ P.support
  · exact Finset.single_le_sum (f := fun d => |coeff d P|) (fun _ _ => abs_nonneg _) h
  · rw [notMem_support_iff.mp h, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem gen {σ : Type} [Fintype σ] (f : σ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).IsHomogeneous 1) (n : ℕ) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ (Q : MvPolynomial σ ℝ) (M : ℝ), Q.IsHomogeneous n →
      (aeval f Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (aeval f Q)| ≤ Cst * M) := by
  classical
  let S : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) n).toFinset
  let B : (σ →₀ ℕ) → ℝ := fun d =>
    ∑ e ∈ (aeval f (monomial d (1 : ℝ))).support, |coeff e (aeval f (monomial d (1 : ℝ)))|
  have hB : ∀ d, 0 ≤ B d := fun d => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ d ∈ S, B d, Finset.sum_nonneg fun d _ => hB d, fun Q M hQ => ⟨?_, fun hM m => ?_⟩⟩
  · simpa using hQ.aeval f hf
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hsub : Q.support ⊆ S := by
      intro d hd
      simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      by_contra hne
      exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero (by omega))
    have e : coeff m (aeval f Q) = ∑ d ∈ Q.support, coeff d Q * coeff m (aeval f (monomial d (1 : ℝ))) := by
      conv_lhs => rw [Q.as_sum]
      rw [map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [← coeff_C_mul]
      congr 1
      have : monomial d (coeff d Q) = C (coeff d Q) * monomial d (1 : ℝ) := by
        rw [C_mul_monomial, mul_one]
      rw [this, map_mul, aeval_C]
      rfl
    rw [e]
    calc _ ≤ ∑ d ∈ Q.support, |coeff d Q * coeff m (aeval f (monomial d (1 : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Q.support, B d * M := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul (abs_coeff_le _ m) (hM d) (abs_nonneg _) (hB d)
      _ ≤ ∑ d ∈ S, B d * M :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => mul_nonneg (hB d) hM0
      _ = _ := by rw [Finset.sum_mul]

theorem gapX_hom {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) : (gapX p).IsHomogeneous 1 := by
  unfold gapX
  refine (isHomogeneous_X ℝ p).sub ?_
  split_ifs
  · exact isHomogeneous_X ℝ _
  · exact isHomogeneous_zero _ _ _

end PositivityTheory.Xgp.poly_towt_bound

theorem PositivityTheory.Xgp.t_poly_towt_bound : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ, (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWt Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWt Q)| ≤ Cst * M)) ∧ ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWtS Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWtS Q)| ≤ Cst * M) := by
  intro Ψ _ N n
  obtain ⟨C1, h1, H1⟩ := PositivityTheory.Xgp.poly_towt_bound.gen (gapX (Ψ := Ψ) (N := N))
    PositivityTheory.Xgp.poly_towt_bound.gapX_hom n
  obtain ⟨C2, h2, H2⟩ := PositivityTheory.Xgp.poly_towt_bound.gen
    (fun o : Option (Ψ × Fin N) => o.elim (X none) fun p => rename some (gapX p)) (by
      rintro (_ | p)
      · exact isHomogeneous_X ℝ _
      · exact (PositivityTheory.Xgp.poly_towt_bound.gapX_hom p).rename_isHomogeneous) n
  refine ⟨C1 + C2, fun Q M hQ => ⟨(H1 Q M hQ).1, fun hM m => ?_⟩,
    fun Q M hQ => ⟨(H2 Q M hQ).1, fun hM m => ?_⟩⟩
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := (H1 Q M hQ).2 hM m
    have h3 := mul_nonneg h2 hM0
    unfold toWt
    linarith
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := (H2 Q M hQ).2 hM m
    have h3 := mul_nonneg h1 hM0
    unfold toWtS
    linarith
