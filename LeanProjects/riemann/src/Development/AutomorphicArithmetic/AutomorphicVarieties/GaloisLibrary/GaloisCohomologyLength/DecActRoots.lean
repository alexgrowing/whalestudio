import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.decActRoots :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (m : ℕ), m.Coprime l → ∀ g ∈ Dec (F := F) A, ∃ k : ℕ, ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l ^ k := by
  intro F Ω _ _ _ _ _ l _ A hA m hm g hg
  have hl : l.Prime := Fact.out
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    exact hl.one_lt.ne' hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hmemA : ∀ ξ : Ω, ξ ^ m = 1 → ξ ∈ A := by
    intro ξ hξ
    rw [← ValuationSubring.valuation_le_one_iff]
    exact (pow_le_one_iff hm0).mp (by rw [← map_pow, hξ, map_one])
  have hgm : (g ζ0) ^ m = 1 := by rw [← map_pow, hζ0.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ0.eq_pow_of_pow_eq_one hgm
  let g' : A.decompositionSubgroup F := ⟨g, hg⟩
  have hlm : ((l : A)) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hA
  haveI : CharP (IsLocalRing.ResidueField A) l := by
    rw [CharP.charP_iff_prime_eq_zero hl]
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  let z0 : A := ⟨ζ0, hmemA ζ0 hζ0.pow_eq_one⟩
  let ω : IsLocalRing.ResidueField A := IsLocalRing.residue A z0
  have hσω : g' • ω = ω ^ a := by
    have hz : g' • z0 = z0 ^ a := Subtype.ext (by
      change g ζ0 = ζ0 ^ a
      exact ha.symm)
    simp only [ω]
    rw [← IsLocalRing.ResidueField.residue_smul, hz, map_pow]
  let σ : IsLocalRing.ResidueField A →ₐ[ZMod l] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g' with
      commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod
        ((MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g').comp
          (algebraMap (ZMod l) (IsLocalRing.ResidueField A)))
        (algebraMap (ZMod l) (IsLocalRing.ResidueField A))) r }
  have hσ : ∀ x, σ x = g' • x := fun x => rfl
  let E := IntermediateField.adjoin (ZMod l) ({ω} : Set (IsLocalRing.ResidueField A))
  have hωE : ω ∈ E := IntermediateField.mem_adjoin_simple_self _ _
  have hint : IsIntegral (ZMod l) ω := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) ?_
    have h1 : ω ^ m = 1 := by
      simp only [ω]
      rw [← map_pow]
      have : z0 ^ m = 1 := Subtype.ext (by
        change ζ0 ^ m = 1
        exact hζ0.pow_eq_one)
      rw [this, map_one]
    rw [h1]
    exact isIntegral_one
  haveI : FiniteDimensional (ZMod l) E := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite E := Module.finite_of_finite (ZMod l)
  have hEle : E ≤ IntermediateField.comap σ E := by
    rw [IntermediateField.adjoin_simple_le_iff]
    show σ ω ∈ E
    rw [hσ, hσω]
    exact pow_mem hωE a
  have hmapE : ∀ x ∈ E, σ x ∈ E := fun x hx => hEle hx
  let τ : E →ₐ[ZMod l] E :=
    { toFun := fun x => ⟨σ x, hmapE x.1 x.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1)
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1)
      commutes' := fun r => Subtype.ext (σ.commutes r) }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) E).2 τ
  have hτω : τ ⟨ω, hωE⟩ = ⟨ω, hωE⟩ ^ (l ^ (n : ℕ)) := by
    rw [← hn]
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hres : ω ^ a = ω ^ (l ^ (n : ℕ)) := by
    have h2 : ((τ ⟨ω, hωE⟩ : E) : IsLocalRing.ResidueField A) = σ ω := rfl
    have := congrArg Subtype.val hτω
    rw [h2] at this
    rw [← hσω, ← hσ]
    simpa using this
  have hfin : g ζ0 = ζ0 ^ (l ^ (n : ℕ)) := by
    rw [← ha]
    have hroot : (ζ0 ^ (l ^ (n : ℕ))) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    have hroota : (ζ0 ^ a) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    refine (UpperTheory.V.LDataCardLeFinrank.ineFixRoots F Ω l A hA m hm _ hroot).1 _ hroota ?_
    have hsub : (z0 ^ a - z0 ^ (l ^ (n : ℕ))) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_pow, sub_eq_zero]
      exact hres
    rw [ValuationSubring.valuation_lt_one_iff] at hsub
    simpa using hsub
  refine ⟨n, fun ζ hζ => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, hfin, ← pow_mul, ← pow_mul, mul_comm]
