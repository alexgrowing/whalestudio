import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePDivGroupLevelCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowNatCastDvdFiniteIntegersAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastFiniteProjectiveAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalSurjectiveOfCotangentSpanTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationsQuotientBialgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAnnihilatedOfAevalMemKerPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTruncationCongrOfPadicContinuousEvalEqZeroStatement

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.exists_coords_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n) (ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n), (∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N) ∧ (∀ n, IsEval p (x n) (ev n)) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n, Function.Surjective (ev n)) ∧ ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, hcou, hres, hspan, hl⟩ := GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates p C v O hv G
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (Fact.out : ¬IsUnit (p : O))
  have hmem : ∀ n i, ¬IsUnit (x n i) := by
    intro n i hu
    have h1 := hu.map (Bialgebra.counitAlgHom O (G.A n))
    rw [Bialgebra.counitAlgHom_apply, hcou n i] at h1
    exact not_isUnit_zero h1
  have hnil : ∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N := fun n i => by
    haveI := hG n
    exact GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra p hp0 C v O hv (G.A n) (x n i) ((IsLocalRing.mem_maximalIdeal _).2 (hmem n i))
  have hex : ∀ n, ∃ E : MvPowerSeries (Fin d) O →ₐ[O] G.A n, IsEval p (x n) E := fun n => by
    haveI := GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra p O (G.A n)
    exact ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O (G.A n) (Fin d) (x n) (hnil n)).1).exists
  choose ev hev using hex
  have hpoly : ∀ n (P : MvPolynomial (Fin d) O),
      ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (x n) P := by
    intro n P
    have h : (ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (x n) :=
      MvPolynomial.algHom_ext fun i => by
        simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (hev n).1 i]
    exact DFunLike.congr_fun h P
  refine ⟨d, x, ev, hnil, hev, hres, hcou, fun n => ?_, fun m N => ?_⟩
  · haveI := hG n
    intro a
    obtain ⟨P, hP⟩ := GlobalTheory.T.aeval_surjective_of_cotangent_span_top O (G.A n) (p : O) hpm (Bialgebra.counitAlgHom O (G.A n)) d (x n)
      (fun i => by rw [Bialgebra.counitAlgHom_apply]; exact hcou n i)
      (fun i => by simpa [map_natCast] using hnil n i) (hspan n) a
    exact ⟨P, (hpoly n P).trans hP⟩
  · obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow d N
    obtain ⟨e, u, hu, hKu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0.ne' p (Fact.out : p.Prime).ne_one
    refine ⟨m + e, fun f hf α hα => ?_⟩
    obtain ⟨P, hPdeg, hPco, hPmem⟩ := GlobalTheory.T.exists_truncation_congr_of_padicContinuousEval_eq_zero p O (G.A (m + e)) d (x (m + e)) (ev (m + e)) (hev _) (m + e) N f hf
    obtain ⟨l, hlx⟩ := hl (m + e)
    let I : Ideal O := Ideal.span {(p : O) ^ (m + e)}
    let l' : Fin d → (G.A (m + e) →ₗ[O] O ⧸ I) :=
      fun i => l i ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (G.A (m + e)))
    obtain ⟨D, hD⟩ := GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra O (G.A (m + e)) I d l' (fun i a b => by
      simp only [l', LinearMap.comp_apply, AugCot.d_mul, map_add, map_smul, Bialgebra.counitAlgHom_apply])
    let φ : G.A (m + e) →ₐ[O] (O ⧸ I) ⊗[O] G.A (m + e) := Algebra.TensorProduct.includeRight
    have hy0 : ∀ j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (φ (x (m + e) j)) = 0 := by
      intro j
      simp [φ, Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul, hcou]
    have hDy : ∀ i j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (D i (φ (x (m + e) j))) =
        if i = j then 1 else 0 := fun i j => (hD i _).trans (hlx i j)
    have hdeg : ∀ β : Fin d →₀ ℕ, N ≤ β.degree →
        MvPolynomial.coeff β (MvPolynomial.map (algebraMap O (O ⧸ I)) P) = 0 := fun β hβ => by
      rw [MvPolynomial.coeff_map, hPdeg β hβ, map_zero]
    have hmemB : MvPolynomial.aeval (fun j => φ (x (m + e) j)) (MvPolynomial.map (algebraMap O (O ⧸ I)) P) ∈
        RingHom.ker (Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e))) ^ N := by
      rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval, AlgHom.comp_apply]
      refine (Ideal.map_le_iff_le_comap.1 ?_) hPmem
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span]
      refine sup_le (Ideal.pow_right_mono ?_ N) ?_
      · rw [Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        exact hy0 j
      · rw [Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
        have h0 : φ ((p : G.A (m + e)) ^ (m + e)) = 0 := by
          rw [map_pow, map_natCast]
          have h1 : ((p : (O ⧸ I) ⊗[O] G.A (m + e))) ^ (m + e) =
              algebraMap (O ⧸ I) _ (Ideal.Quotient.mk I ((p : O) ^ (m + e))) := by
            rw [map_pow, map_pow, map_natCast, map_natCast]
          rw [h1, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
        rw [SetLike.mem_coe, h0]
        exact zero_mem _
    have key := hK (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) _ _ D hy0 hDy _ hdeg hmemB α
    rw [MvPolynomial.coeff_map, ← map_natCast (algebraMap O (O ⧸ I)), ← map_mul,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at key
    rw [← hPco α hα]
    have hpO : (p : O) ≠ 0 := by
      intro h
      have h2 := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at h2
      exact hp0 (by exact_mod_cast h2)
    have hunit : IsUnit (u : O) := by
      by_contra hnu
      have hcop : IsCoprime (u : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2
        ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hu)))
      obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom O)
      have h3 : a * Int.castRingHom O u + b * Int.castRingHom O p ∈ IsLocalRing.maximalIdeal O := by
        refine add_mem (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
        · simpa using (IsLocalRing.mem_maximalIdeal _).2 hnu
        · simpa using hpm
      rw [hab] at h3
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
    rw [hKu, Nat.cast_mul, Nat.cast_pow, pow_add, mul_assoc, mul_comm ((p : O) ^ m)] at key
    have key2 := (mul_dvd_mul_iff_left (pow_ne_zero e hpO)).1 key
    exact (hunit.dvd_mul_left).1 key2
