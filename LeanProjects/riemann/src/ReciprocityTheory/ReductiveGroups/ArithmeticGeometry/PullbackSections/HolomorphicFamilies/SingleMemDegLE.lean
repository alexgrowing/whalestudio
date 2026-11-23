import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD

open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

variable {V : Type} [CommRing V]

theorem aeval_tan {ι : Type} [DecidableEq ι] (ℓ : ι) (P : MvPolynomial ι V) :
    aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) P =
      algebraMap V (DualNumber V) (constantCoeff P) + coeff (Finsupp.single ℓ 1) P • DualNumber.eps := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.constantCoeff_C, MvPolynomial.coeff_C,
      if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_smul, add_zero]
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, MvPolynomial.coeff_add, add_smul]; abel
  | mul_X p n hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, zero_add,
      MvPolynomial.coeff_mul_X']
    by_cases h : n = ℓ
    · subst h
      have hs : n ∈ (Finsupp.single n (1 : ℕ)).support := by simp
      rw [if_pos rfl, if_pos hs, tsub_self, ← MvPolynomial.constantCoeff_eq, add_mul, smul_mul_assoc,
        DualNumber.eps_mul_eps, smul_zero, add_zero, Algebra.smul_def]
    · have : n ∉ (Finsupp.single ℓ 1).support := by simp [Finsupp.support_single_ne_zero, Ne.symm h, h]
      simp [h, this]

theorem coeff_psTrunc {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι V) (e : ι →₀ ℕ)
    (he : e ∈ degLE m) : coeff e (psTrunc m f) = MvPowerSeries.coeff e f := by
  simp [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he]

theorem single_mem_degLE {ι : Type} [Fintype ι] [DecidableEq ι] (ℓ : ι) : Finsupp.single ℓ 1 ∈ degLE (ι := ι) 1 := by
  simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨fun i => if i = ℓ then 1 else 0, ?_⟩, ?_⟩
  · ext i
    by_cases h : i = ℓ
    · subst h; simp
    · simp [h, Finsupp.single_apply, Ne.symm h]
  · simp [Finsupp.sum_single_index]

theorem ker_jetAug_sq {κ : Type} : (RingHom.ker (jetAug (R := V) (ι := κ) (m := 1))) ^ (1 + 1) = ⊥ := by
  exact ReciprocityTheory.ChartRestriction.G.Chart.ker_jetAug_pow κ 1

end Alg

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
