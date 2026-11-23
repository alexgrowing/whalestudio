import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjOfFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClNorm0
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIntegral
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoPoint

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J

private theorem aeval_X_ne {O : Type} [CommRing O] {d : ℕ} (i : Fin d) {p : Polynomial O} (hp : p ≠ 0) :
    Polynomial.aeval (MvPowerSeries.X i : MvPowerSeries (Fin d) O) p ≠ 0 := by
  classical
  intro h
  apply hp
  ext n
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single i n)) h
  have h2 : ∀ k, MvPowerSeries.coeff (Finsupp.single i n) (p.coeff k • (MvPowerSeries.X i : MvPowerSeries (Fin d) O) ^ k) =
      if k = n then p.coeff k else 0 := by
    intro k
    rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X_pow]
    by_cases hk : k = n
    · subst hk
      simp
    · have : Finsupp.single i n ≠ Finsupp.single i k := fun e => hk (Finsupp.single_injective i e).symm
      simp [hk, this]
  rw [Polynomial.aeval_eq_sum_range, map_sum] at h1
  simp only [h2] at h1
  rw [Finset.sum_ite_eq', map_zero] at h1
  split_ifs at h1 with hn
  · simpa using h1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn)]
    simp

private theorem fin_of_alg (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (C : Type) [CommRing C] [Algebra O C] [IsLocalRing C] [IsDomain C]
    (hC : UpperTheory.V.CA.IsCL O C) (hinj : Function.Injective (algebraMap O C))
    (halg : ∀ x : C, IsAlgebraic O x) : Module.Finite O C := by
  obtain ⟨d, φ, hφ, -, -, hd⟩ := (UpperTheory.V.CA.cl_nn O C hC).1 hinj
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · exact UpperTheory.V.CA.cl_norm0 O C hC (by simpa using hd) hinj
  · exfalso
    obtain ⟨p, hp, h0⟩ := halg (φ (MvPowerSeries.X ⟨0, hpos⟩))
    apply aeval_X_ne (⟨0, hpos⟩ : Fin d) hp
    apply hφ
    rw [← Polynomial.aeval_algHom_apply, h0, map_zero]

private theorem norm_le_one_of_int {A K : Type} [CommRing A] [NormedField K] [IsUltrametricDist K] [Algebra A K]
    (hA : ∀ a : A, ‖algebraMap A K a‖ ≤ 1) {x : K} (hx : IsIntegral A x) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIntegral.norm_le_one_of_int hA hx

private theorem mem_rad {O C : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing C]
    [IsLocalRing C] [Algebra O C] [Algebra.IsIntegral O C] {t : O} (ht : t ≠ 0) {a : C}
    (ha : a ∈ maximalIdeal C) : a ∈ (Ideal.span {algebraMap O C t}).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro p ⟨hle, hp⟩
  have hq : (p.comap (algebraMap O C)).IsPrime := Ideal.comap_isPrime _ _
  have hne : p.comap (algebraMap O C) ≠ ⊥ := fun h => ht (by
    have h1 : t ∈ p.comap (algebraMap O C) := hle (Ideal.mem_span_singleton_self _)
    exact (Ideal.mem_bot).1 (h ▸ h1))
  haveI : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  have hmax : (p.comap (algebraMap O C)).IsMaximal := IsPrime.to_maximal_ideal hne
  have hpm : p.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p hmax
  rw [IsLocalRing.eq_maximalIdeal hpm]
  exact ha

end UpperTheory.V.J

theorem UpperTheory.V.J.coPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (y : R →ₐ[c.O] Qbar l),
        Module.Finite c.O y.range ∧ (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal R, ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.CoPoint.coPt
