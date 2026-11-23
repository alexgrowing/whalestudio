import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (h : ζ ^ n = 1) (h1 : ζ ≠ 1) :
    ζ - 1 ∣ (n : O) := by
  have hS : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have hg := mul_geom_sum ζ n
    rw [h, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr h1)
  have hn : (n : O) = ∑ i ∈ Finset.range n, (1 - ζ ^ i) := by
    rw [Finset.sum_sub_distrib, hS, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
  rw [hn]
  apply Finset.dvd_sum
  intro i _
  have hd := sub_dvd_pow_sub_pow ζ 1 i
  rw [one_pow] at hd
  rw [← neg_sub (ζ ^ i) 1]
  exact (dvd_neg).mpr hd

theorem UpperTheory.V.Chr.rootVal :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (n : ℕ), n ≠ 0 → IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O ∧
          (∀ ζ : O, ζ ^ n = 1 → ζ ≠ 1 → IsDiscreteValuationRing.addVal O (ζ - 1) ≤ (n.factorization l : ℕ∞) * eO l O) ∧ eO l O ≠ ⊤ ∧ CharZero O := by
  intro l _ O _ _ _ _ _ n hn
  obtain ⟨hiO, -, -, -, -, -, -, hvO, hunit⟩ := dvrFacts l O
  have hp : l.Prime := Fact.out
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hlO : (l : O) ≠ 0 := by
    intro h
    apply hl0
    apply hiO
    rw [map_natCast, h, map_zero]
  have hval : IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O := by
    have hu : IsUnit ((n / l ^ n.factorization l : ℕ) : O) := hunit _ (Nat.not_dvd_ordCompl hp hn)
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l]
    rw [Nat.cast_mul, Nat.cast_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hu,
      add_zero, hvO, nsmul_eq_mul]
  refine ⟨hval, ?_, ?_, ?_⟩
  · intro ζ hζ h1
    rw [← hval]
    exact (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr (sub_one_dvd hζ h1)
  · rw [hvO]
    exact fun h => hlO ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
  · exact charZero_of_injective_algebraMap hiO
