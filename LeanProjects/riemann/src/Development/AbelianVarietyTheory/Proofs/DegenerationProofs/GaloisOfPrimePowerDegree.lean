import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSubMemMaximalIdeal

namespace GlobalTheory.TameKummer

open IsLocalRing Polynomial

theorem exists_pow_eq_of_residue {R : Type*} [CommRing R] [HenselianLocalRing R] {n : ℕ}
    (hn : IsUnit (n : R)) {u : R} (hu : IsUnit u) (c : ResidueField R)
    (hc : c ^ n = residue R u) : ∃ v : R, v ^ n = u ∧ residue R v = c := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨a, rfl⟩ := residue_surjective c
  have ha : IsUnit a := by
    have : IsUnit (residue R a ^ n) := hc ▸ hu.map _
    exact (isUnit_map_iff (residue R) a).1 ((isUnit_pow_iff hn0).1 this)
  obtain ⟨v, hv, hva⟩ := HenselianLocalRing.is_henselian (X ^ n - C u : R[X])
    (monic_X_pow_sub_C u hn0) a
    (by rw [← residue_eq_zero_iff]; simp [hc])
    (by simpa [derivative_X_pow] using hn.mul (ha.pow _))
  refine ⟨v, ?_, ?_⟩
  · simpa [sub_eq_zero] using hv
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hva
    exact hva

theorem exists_isPrimitiveRoot {R : Type*} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] {n : ℕ} (hn : IsUnit (n : R)) :
    ∃ v : R, IsPrimitiveRoot v n := by
  have : NeZero (n : ResidueField R) := ⟨by simpa using (hn.map (residue R)).ne_zero⟩
  obtain ⟨c, hc⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField R) n
  obtain ⟨v, hv, hvc⟩ := exists_pow_eq_of_residue hn isUnit_one c (by simpa using hc.pow_eq_one)
  refine ⟨v, hv, fun d hd => hc.dvd_of_pow_eq_one d ?_⟩
  rw [← hvc, ← map_pow, hd, map_one]

theorem irreducible_X_pow_sub_C {R : Type*} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {π : R}
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) :
    Irreducible (X ^ n - C (algebraMap R K π) : K[X]) := by
  have hm := monic_X_pow_sub_C π hn
  have h : Irreducible (X ^ n - C π : R[X]) := by
    refine irreducible_of_eisenstein_criterion (P := Ideal.span {π})
      ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ.prime) ?_ ?_ ?_ ?_ hm.isPrimitive
    · rw [hm.leadingCoeff, Ideal.mem_span_singleton]
      exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
    · intro i hi
      rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn), Nat.cast_lt] at hi
      rw [coeff_sub, coeff_X_pow, if_neg hi.ne, coeff_C, Ideal.mem_span_singleton]
      split_ifs <;> simp
    · rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)]
      exact_mod_cast Nat.pos_of_ne_zero hn
    · rw [coeff_sub, coeff_X_pow, if_neg hn.symm, coeff_C, if_pos rfl, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, zero_sub, dvd_neg]
      intro h
      have : π * π ∣ π * 1 := by simpa [sq] using h
      exact hπ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hπ.ne_zero).1 this))
  simpa using (hm.irreducible_iff_irreducible_map_fraction_map (K := K)).1 h

theorem minpoly_eq {R : Type*} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {π : R}
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) {L : Type*} [Field L] [Algebra K L] {ρ : L}
    (hρ : ρ ^ n = algebraMap K L (algebraMap R K π)) :
    minpoly K ρ = X ^ n - C (algebraMap R K π) :=
  (minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C K hπ hn) (by simp [hρ])
    (monic_X_pow_sub_C _ hn)).symm

theorem isLocalRing_of_finite (R S : Type*) [CommRing R] [HenselianLocalRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  have e : S ≃+* Localization.AtPrime q := RingEquiv.ofBijective (algebraMap _ _)
    ⟨IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors,
      surjective_algebraMap_localization_of_henselian R q⟩
  exact e.symm.isLocalRing

theorem exists_root {R : Type} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hn : IsUnit ((Module.finrank K L : ℕ) : R)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  first
  | exact @_root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq
  | exact _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq
  | (apply _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq ..)

theorem mem_range_of_pow_eq_one {R : Type*} (K : Type*) [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
    (hn : IsUnit (n : R)) {Ω : Type*} [Field Ω] [Algebra K Ω] {ζ : Ω} (hζ : ζ ^ n = 1) :
    ζ ∈ Set.range (algebraMap K Ω) := by
  have : NeZero n := ⟨by
    rintro rfl
    simp at hn⟩
  obtain ⟨v, hv⟩ := exists_isPrimitiveRoot hn
  have h := (hv.map_of_injective (f := algebraMap R K) (IsFractionRing.injective R K)).map_of_injective
    (f := algebraMap K Ω) (algebraMap K Ω).injective
  obtain ⟨i, -, rfl⟩ := h.eq_pow_of_pow_eq_one hζ
  exact ⟨_, map_pow _ _ _⟩

theorem isClosed_eval {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]
    (x : Ω) (s : Set Ω) : IsClosed {σ : Ω ≃ₐ[K] Ω | σ x ∈ s} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)), ?_,
    (stabilizer_isOpen_of_isIntegral x).preimage (by fun_prop), ?_⟩
  · intro τ hτ
    have h : σ.symm (τ x) = x := hτ
    have h' : τ x = σ x := by rw [← σ.symm_apply_eq.1 h]
    simpa [h'] using hσ
  · simp

theorem exists_generator {R : Type*} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    {l : ℕ} (hl : IsUnit (l : R)) (Ω : Type*) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    ∃ σ : Ω ≃ₐ[K] Ω, ∀ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) →
      ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : IsGalois K Ω := {}
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have hlm : ∀ m, IsUnit ((l ^ m : ℕ) : R) := fun m => by simpa using hl.pow m
  have hπ0 : algebraMap K Ω (algebraMap R K π) ≠ 0 := by
    simpa using hπ.ne_zero
  let G : ℕ → Set (Ω ≃ₐ[K] Ω) := fun m => {σ | ∀ ρ : Ω,
    ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ}
  have hcl : ∀ m, IsClosed (G m) := fun m => by
    have : G m = ⋂ ρ : Ω, {σ : Ω ≃ₐ[K] Ω | σ ρ ∈ {y | ρ ^ l ^ m =
        algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ y = ζ * ρ}} := by
      ext σ
      simp [G]
    rw [this]
    exact isClosed_iInter fun ρ => isClosed_eval ρ _
  have hdec : ∀ m, G (m + 1) ⊆ G m := fun m σ hσ ρ hρ => by
    obtain ⟨ρ', rfl⟩ := IsAlgClosed.exists_pow_nat_eq ρ (Nat.pos_of_ne_zero hl0)
    obtain ⟨ζ, hζ, h⟩ := hσ ρ' (by rw [← hρ, ← pow_mul, pow_succ'])
    refine ⟨ζ ^ l, hζ.pow (Nat.pos_of_ne_zero (pow_ne_zero _ hl0)) (pow_succ' _ _), ?_⟩
    rw [map_pow, h, mul_pow]
  have hne : ∀ m, (G m).Nonempty := fun m => by
    have hn : l ^ m ≠ 0 := pow_ne_zero _ hl0
    obtain ⟨ρ₀, hρ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (algebraMap R K π))
      (Nat.pos_of_ne_zero hn)
    have h0 : ρ₀ ≠ 0 := by
      rintro rfl
      exact hπ0 (by rw [← hρ₀, zero_pow hn])
    obtain ⟨v, hv⟩ := exists_isPrimitiveRoot (hlm m)
    have hζ := (hv.map_of_injective (f := algebraMap R K)
      (IsFractionRing.injective R K)).map_of_injective
      (f := algebraMap K Ω) (algebraMap K Ω).injective
    set ζ := algebraMap K Ω (algebraMap R K v)
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (x := ζ * ρ₀) (y := ρ₀) (K := K)
      (Algebra.IsAlgebraic.isAlgebraic _)
      (by rw [minpoly_eq K hπ hn hρ₀]; simp [mul_pow, hζ.pow_eq_one, hρ₀])
    refine ⟨σ, fun ρ hρ => ⟨ζ, hζ, ?_⟩⟩
    obtain ⟨η, hη⟩ := mem_range_of_pow_eq_one K (hlm m) (ζ := ρ / ρ₀)
      (by rw [div_pow, hρ, hρ₀, div_self hπ0])
    have : ρ = algebraMap K Ω η * ρ₀ := by rw [hη, div_mul_cancel₀ _ h0]
    rw [this, map_mul, AlgEquiv.commutes, hσ]
    ring
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed G hdec hne
    (hcl 0).isCompact hcl
  exact ⟨σ, fun m => Set.mem_iInter.1 hσ m⟩

theorem le_adjoin_root {R : Type} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    {Ω : Type} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hn : IsUnit ((Module.finrank K L : ℕ) : R)) :
    ∃ ρ : Ω, ρ ^ Module.finrank K L = algebraMap K Ω (algebraMap R K π) ∧
      L ≤ IntermediateField.adjoin K {ρ} := by
  obtain ⟨ρ, hρ⟩ := exists_root K hH hπ L hn
  have hn0 : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hρ' : (ρ : Ω) ^ Module.finrank K L = algebraMap K Ω (algebraMap R K π) := by
    have := congrArg (algebraMap L Ω) hρ
    rwa [map_pow, ← IsScalarTower.algebraMap_apply] at this
  refine ⟨ρ, hρ', ge_of_eq (IntermediateField.eq_of_le_of_finrank_eq ?_ ?_)⟩
  · simp
  · have hi : IsIntegral K (ρ : Ω) := (Algebra.IsIntegral.isIntegral (R := K) ρ).map L.val
    rw [IntermediateField.adjoin.finrank hi, minpoly_eq K hπ hn0 hρ', natDegree_X_pow_sub_C]

end GlobalTheory.TameKummer

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.TameKummer.galois_of_prime_power_degree : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [CharZero K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (l : ℕ), l.Prime → IsUnit (l : R) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∃ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) ∧ L ≤ IntermediateField.adjoin K {ρ}) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → ζ ∈ Set.range (algebraMap K Ω)) ∧ ∃ σ : Ω ≃ₐ[K] Ω, ∀ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ := by
  rintro R K _ _ _ _ _ _ ⟨h1, h2, h3, h4⟩ π hπ l hl hu Ω _ _ _
  obtain rfl : ‹IsLocalRing R› = h2.toIsLocalRing := rfl
  refine ⟨fun L hL hN hp => ?_, fun m ζ hζ => ?_, GlobalTheory.TameKummer.exists_generator K h2 hπ hu Ω⟩
  · have : IsGalois K L := {}
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
    rw [IsGalois.card_aut_eq_finrank] at hm
    obtain ⟨ρ, h⟩ := GlobalTheory.TameKummer.le_adjoin_root K h2 hπ L (by rw [hm]; simpa using hu.pow m)
    exact ⟨m, ρ, hm ▸ h⟩
  · exact GlobalTheory.TameKummer.mem_range_of_pow_eq_one (R := R) K (by simpa using hu.pow m) hζ
