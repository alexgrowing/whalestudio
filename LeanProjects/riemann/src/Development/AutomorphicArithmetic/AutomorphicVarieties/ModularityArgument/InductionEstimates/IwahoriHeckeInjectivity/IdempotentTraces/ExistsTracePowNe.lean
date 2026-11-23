import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AlgTrace

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem exists_trace_pow_ne {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (R : Module.End ℂ W) (hR : Function.Injective R) : ∃ j : ℕ, LinearMap.trace ℂ W (R ^ (j + 1)) ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : R.charpoly.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hm0⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff R).1 h0
    exact hm (hR (by rw [hm0, map_zero]))
  have h1 := congrArg (LinearMap.trace ℂ W) (LinearMap.aeval_self_charpoly R)
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ', map_add, map_sum, map_zero] at h1
  simp only [map_smul, h, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, LinearMap.trace_one, smul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact h0 h2
  · exact (Module.finrank_pos (R := ℂ) (M := W)).ne' (by exact_mod_cast h2)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.finTw :
    FinTw := by
  intro W X _ _ _ _ T hc hirr U hU i x hinj
  obtain ⟨c, hc0, H⟩ := UpperTheory.ConvolutionTheory.L1.algTrace W X 1 T
    (by
      intro a b hab y z
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · exact hc y z
      · exact (hc z y).symm
      · exact absurd rfl hab) hirr U hU
  have hcom : ∀ (k : ℕ) (j : Fin 2), j ≠ i → ∀ y, Commute (T i x ^ k) (T j y) := by
    intro k j hj y
    apply Commute.pow_left
    fin_cases i <;> fin_cases j
    · exact absurd rfl hj
    · exact hc x y
    · exact (hc y x).symm
    · exact absurd rfl hj
  rw [Filter.frequently_atTop]
  intro N
  have hN : Function.Injective (T i x ^ N : Module.End ℂ W) := by
    rw [Module.End.coe_pow]
    exact hinj.iterate N
  obtain ⟨j, hj⟩ := exists_trace_pow_ne _ hN
  refine ⟨N * (j + 1), Nat.le_mul_of_pos_right N j.succ_pos, ?_⟩
  rw [H i _ (hcom _), pow_mul]
  exact mul_ne_zero hc0 hj
