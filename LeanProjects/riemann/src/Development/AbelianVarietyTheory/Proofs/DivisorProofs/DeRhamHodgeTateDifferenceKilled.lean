import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVolumeParameterMaxTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVolumeKillsDifferenceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.HTVert

open MvPolynomial Formalism.BasicNotions.DV

theorem sub_mem_span_range {σ A : Type} [CommRing A] [Algebra ℝ A] (f g : MvPolynomial σ ℝ →ₐ[ℝ] A)
    (Q : MvPolynomial σ ℝ) : f Q - g Q ∈ Ideal.span (Set.range fun i => f (X i) - g (X i)) := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [← MvPolynomial.algebraMap_eq, f.commutes, g.commutes, sub_self]; exact zero_mem _
  | add P Q hP hQ => rw [map_add, map_add, add_sub_add_comm]; exact Ideal.add_mem _ hP hQ
  | mul_X P i hP =>
    have e : f (P * X i) - g (P * X i) = (f P - g P) * f (X i) + g P * (f (X i) - g (X i)) := by
      simp only [map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hP) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem tagDR_sub_tagHT (Tau : Type) [Fintype Tau] (N : ℕ) (Q : MvPolynomial (Rt Tau N) ℝ) :
    ∃ c : Rt Tau N → MvPolynomial (Vm Tau N) ℝ,
      tagDR Tau N Q - tagHT Tau N Q = ∑ y, (X (Sum.inl (false, y)) - X (Sum.inl (true, y))) * c y := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (sub_mem_span_range (tagDR Tau N) (tagHT Tau N) Q)
  refine ⟨c, hc.symm.trans (Finset.sum_congr rfl fun y _ => ?_)⟩
  simp [tagDR, tagHT, mul_comm]

end GlobalTheory.HTVert

open MvPolynomial Formalism.BasicNotions.DV in

theorem GlobalTheory.HTVert.onObj_aux1tAt_of_knownResults : Hypotheses2 → HypothesesH → OnObj fun _ O _ _ _ _ => DeRhamHodgeTateDifferenceKilledAt O.Y := by
  intro h2 hH D O hO _ A T H h Sx R p hp τ k hk Q
  obtain ⟨c, hc⟩ := GlobalTheory.HTVert.tagDR_sub_tagHT D.what₂.Tau O.Y.N Q
  rw [hc, GlobalTheory.T.arithmetic_mixed_volume_parameter_max_two D O hO, Finset.mul_sum, map_sum]
  exact Finset.sum_eq_zero fun y _ => GlobalTheory.T.arithmetic_mixed_volume_kills_difference h2 hH D O hO Sx _ (le_max_right _ _) p hp τ k hk y (c y)
