import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.NormalPole

theorem exists_height_one {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (f : K) (Q : Ideal R)
    (hQ : ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ Q) [Q.IsPrime] :
    ∃ p : Ideal R, p.IsPrime ∧ p ≤ Q ∧ p.height = 1 ∧
      ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ p := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R K c ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hc0
  let d : Ideal R := (Ideal.span {c}).colon {b}
  have hd : ∀ s, s ∈ d ↔ c ∣ s * b := fun s => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  have reg : ∀ s, (∃ e : R, algebraMap R K s * (algebraMap R K b / algebraMap R K c) =
      algebraMap R K e) ↔ s ∈ d := fun s => by
    rw [hd]
    refine exists_congr fun e => ?_
    rw [← mul_div_assoc, div_eq_iff hcK, ← map_mul, ← map_mul, (IsFractionRing.injective R _).eq_iff,
      mul_comm e]
  have hdQ : d ≤ Q := fun s hs => by
    obtain ⟨e, he⟩ := (reg s).2 hs
    exact hQ s e he
  obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hdQ
  have hpa : p ∈ associatedPrimes R (R ⧸ d) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [Ideal.annihilator_quotient]
    exact hp
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hpa
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : p.height = 1 := height_eq_one_of_forall_mem_iff_dvd (b := x * b) hc0 fun r => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hd, _root_.mul_assoc]
  exact ⟨p, hpp, hpQ, h1, fun s e he => hp.1.2 ((reg s).1 ⟨e, he⟩)⟩

theorem mem_range_iff {R B K : Type} [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra R K]
    [Algebra B K] [IsScalarTower R B K] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime B p] (f : K) :
    (∃ a : B, algebraMap B K a = f) ↔
      ∃ s c : R, algebraMap R K s * f = algebraMap R K c ∧ s ∉ p := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj p.primeCompl a
    refine ⟨s, c, ?_, s.2⟩
    rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K c, ← map_mul,
      mul_comm, e]
  · rintro ⟨s, c, e, hs⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units B (⟨s, hs⟩ : p.primeCompl)
    refine ⟨↑u⁻¹ * algebraMap R B c, ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← e, IsScalarTower.algebraMap_apply R B K s]
    have hu' : algebraMap R B s = u := hu.symm
    rw [hu', ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]

theorem exists_zeroAt_inv : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (x : X) (f : X.functionField), ¬ RegAt x f → ∃ z : X, z ⤳ x ∧ ZeroAt z f⁻¹ := by
  intro X _ _ hN x f hf
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI := isIntegrallyClosed_sections_of_stalks (fun y => (hN y).2) hU
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have key : ∀ y : U, RegAt (y : X) f ↔ ∃ s c : Γ(X, U), algebraMap _ X.functionField s * f =
      algebraMap _ X.functionField c ∧ s ∉ (hU.primeIdealOf y).asIdeal := fun y =>
    haveI := hU.isLocalization_stalk y
    mem_range_iff (B := X.presheaf.stalk (y : X)) (hU.primeIdealOf y).asIdeal f
  obtain ⟨p, hp, hpQ, h1, hpf⟩ := exists_height_one f (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    fun s c e => by_contra fun hs => hf ((key ⟨x, hx⟩).2 ⟨s, c, e, hs⟩)
  let P : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ x := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hpQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
  have hfz : ¬ RegAt (z : X) f := fun h => by
    obtain ⟨s, c, e, hs⟩ := (key z).1 h
    rw [hP] at hs
    exact hs (hpf s c e)
  clear_value z
  haveI := hU.isLocalization_stalk z
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    isDiscreteValuationRing_of_height_eq_one (hU.primeIdealOf z).asIdeal (by rw [hP]; exact h1) _
  refine ⟨z, hzx, zeroAt_iff.2 ⟨?_, fun h => hfz ?_⟩⟩
  · exact (ValuationRing.isInteger_or_isInteger (X.presheaf.stalk (z : X)) f).resolve_left hfz
  · simpa using h.inv.regAt

end GlobalTheory.NormalPole
