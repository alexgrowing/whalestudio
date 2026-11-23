import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem dense_mvPolynomial_eval_ne_zero {D : ℕ} (q : MvPolynomial (Fin D) ℂ) (hq : q ≠ 0) :
    Dense {z : Fin D → ℂ | MvPolynomial.eval z q ≠ 0} := by
  rw [Metric.dense_iff]
  intro z₀ r hr
  by_contra hne
  apply hq
  refine MvPolynomial.funext_set (fun i => Metric.ball (z₀ i) r)
    (fun i => infinite_of_mem_nhds (z₀ i) (Metric.ball_mem_nhds _ hr)) (fun x hx => ?_)
  rw [map_zero]
  by_contra hx0
  apply hne
  refine ⟨x, ?_, hx0⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  exact fun i => hx i (Set.mem_univ i)

theorem exists_algIndep_tuple_near :
    ∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0 := by
  intro K _ _ sg D z₀ ε hε
  let S : {p : MvPolynomial (Fin D) K // p ≠ 0} → Set (Fin D → ℂ) :=
    fun p => {z | MvPolynomial.eval z (MvPolynomial.map sg p.1) ≠ 0}
  have : Countable (MvPolynomial (Fin D) K) := by
    refine Function.Surjective.countable (f := fun l : List ((Fin D →₀ ℕ) × K) =>
      (l.map fun mc => MvPolynomial.monomial mc.1 mc.2).sum) fun p => ?_
    refine ⟨p.support.toList.map fun m => (m, MvPolynomial.coeff m p), ?_⟩
    simp only [List.map_map]
    rw [Finset.sum_map_toList]
    exact p.as_sum.symm
  have hS : Dense (⋂ p, S p) := by
    apply dense_iInter_of_isOpen
    · intro p
      exact isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    · intro p
      refine dense_mvPolynomial_eval_ne_zero _ fun h0 => p.2 ?_
      exact MvPolynomial.map_injective sg sg.injective (h0.trans (map_zero _).symm)
  obtain ⟨z, hzS, hz⟩ := hS.exists_mem_open (Metric.isOpen_ball (x := z₀)) (Metric.nonempty_ball.mpr hε)
  refine ⟨z, ?_, fun p hp => ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε] at hz
    intro i
    rw [← dist_eq_norm]
    exact hz i
  · rw [← MvPolynomial.eval_map]
    exact Set.mem_iInter.mp hzS ⟨p, hp⟩

end GlobalTheory
