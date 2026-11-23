import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NoetherNormalizationChart
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PseudoDivision

theorem UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof.{u} :
    GroundTheory.Heights₂.Heights.GenericNoetherNormalisation.Statement.{u} := by
  intro A _ _ n q _ hq _
  classical
  obtain ⟨f, hfq, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  obtain ⟨e, a, ha, hlc⟩ := UpperTheory.exists_monic_change_of_variables A n f hf
  have hg : e f ≠ 0 := fun h ↦ hf (e.injective (by simpa using h))
  let π : Polynomial (MvPolynomial (Fin n) A) →ₐ[A] MvPolynomial (Fin (n + 1)) A ⧸ q :=
    (Ideal.Quotient.mkₐ A q).comp e.symm.toAlgHom
  have hπf : π (e f) = 0 := by
    simpa [π, Ideal.Quotient.eq_zero_iff_mem] using hfq
  have hsurj : Function.Surjective π :=
    (Ideal.Quotient.mkₐ_surjective A q).comp e.symm.surjective
  let z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q :=
    fun i ↦ π (Polynomial.C (MvPolynomial.X i))
  have hz : ∀ c : MvPolynomial (Fin n) A, MvPolynomial.aeval z c = π (Polynomial.C c) := by
    intro c
    have : MvPolynomial.aeval z = π.comp (Polynomial.CAlgHom) := by
      ext i
      simp [z]
    rw [this]
    rfl
  let N := (e f).natDegree
  refine ⟨a, ha, z, (Finset.range N).image (fun j ↦ π Polynomial.X ^ j), fun d ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hsurj d
  obtain ⟨k, s, r, hk, hr⟩ := UpperTheory.pseudo_division (MvPolynomial (Fin n) A) (e f) p hg
  have h1 : a ^ k • π p = π r := by
    have := congrArg π hk
    rw [map_add, map_mul π (e f), hπf, zero_mul, zero_add, hlc, map_mul, ← hz, ← map_pow,
      MvPolynomial.aeval_C, ← Algebra.smul_def] at this
    exact this
  have h2 : r = ∑ j ∈ Finset.range N, Polynomial.C (r.coeff j) * Polynomial.X ^ j := by
    rw [Polynomial.degree_eq_natDegree hg] at hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        Polynomial.as_sum_range' r N ((Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hr)
  refine ⟨k, fun t ↦ ∑ j ∈ Finset.range N with π Polynomial.X ^ j = t, r.coeff j, ?_⟩
  rw [h1, h2, map_sum, ← Finset.sum_fiberwise_of_maps_to (g := fun j ↦ π Polynomial.X ^ j)
    (fun j hj ↦ Finset.mem_image_of_mem _ hj), ← h2]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [map_mul, map_pow, hz, (Finset.mem_filter.mp hj).2]
