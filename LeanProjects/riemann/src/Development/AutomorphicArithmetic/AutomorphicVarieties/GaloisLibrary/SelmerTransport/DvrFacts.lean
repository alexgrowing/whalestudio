import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

section Alg

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

private theorem algebraMap_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := hp.isMaximal hne
  have hbot : (⊥ : Ideal O).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l])
    rw [← RingHom.ker_eq_comap_bot]
    exact hmax
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm

private theorem length_quot [Module.Free ℤ_[l] O] : Module.length ℤ_[l] (O ⧸ Ideal.span {(l : O)}) = Module.finrank ℤ_[l] O := by
  have hspan : Ideal.span {(l : O)} = (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hspan, ← IsLocalRing.finrank_quotient_map (R := ℤ_[l]) (S := O)]
  letI : Field (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l]) := Ideal.Quotient.field _
  haveI : Module.Finite (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l])
      (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  rw [← Module.length_eq_finrank]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

end Alg

theorem UpperTheory.V.Base.dvrFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧
      eO l O = Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) ∧ eO l O ≠ 0 ∧
      eO l O ≤ (Module.finrank ℤ_[l] O : ℕ∞) ∧ eO l O = IsDiscreteValuationRing.addVal O (l : O) ∧
      ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : O) := by
  intro l _ O _ _ _ _ _
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := algebraMap_inj O
  haveI : CharZero O := charZero_of_injective_algebraMap hinj
  obtain ⟨hcomp, -, hlm, -, hfree, hloc⟩ := UpperTheory.V.abelian₂.dvr_finite l O
  haveI := hfree
  haveI := hloc
  have hspan : Ideal.span {(l : O)} =
      (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by
      rw [map_natCast, h, map_zero]
    have h'' : ((l : ℕ) : ℤ_[l]) = 0 := hinj h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h'')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hval : IsDiscreteValuationRing.addVal O (l : O) = n :=
    IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  have he : eO l O = n := by
    show Module.length O (O ⧸ Ideal.span {(l : O)}) = n
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) n
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hlm (hu ▸ u.isUnit)
  refine ⟨hinj, hfree, hloc, hcomp, ?_, ?_, ?_, ?_, ?_⟩
  · show Module.length O (O ⧸ Ideal.span {(l : O)}) = _
    rw [hspan]
  · rw [he]
    exact_mod_cast hn0
  · rw [← length_quot (l := l) O]
    show Module.length O (O ⧸ Ideal.span {(l : O)}) ≤ _
    rw [IsLocalRing.length_restrictScalars ℤ_[l] O (O ⧸ Ideal.span {(l : O)})]
    exact le_mul_of_one_le_right' (Order.one_le_iff_pos.2 Module.length_pos)
  · rw [he, hval]
  · intro m hm
    have hcop : IsCoprime (l : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
    obtain ⟨a, b, hab⟩ := hcop
    by_contra hmu
    have hmm : (m : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hmu
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have hab' : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → O) hab
      rw [← hab']
      exact add_mem (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hmm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
