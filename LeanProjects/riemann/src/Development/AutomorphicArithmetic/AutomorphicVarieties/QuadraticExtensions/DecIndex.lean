import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IdxAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecFrob

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.decIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p c : ℕ) (A₀ : ValuationSubring Ω), p.Prime → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → A₀.valuation (p : Ω) < 1 →
      ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≠ 0 ∧ ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≤ c := by
  intro Ω _ _ _ p c A₀ hp hc hA
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, hgζ⟩ := decFrob Ω p A₀ hA
  have hodd : Nat.Coprime 2 p := by
    rw [Nat.coprime_two_left, Nat.odd_iff]; omega
  have hu : ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2]) = p := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 ^ n)
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val :=
      cyclotomicCharacter.spec 2 (n := n) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) ζ hζ.pow_eq_one
    have h2 := hgζ (2 ^ n) (Nat.Coprime.pow_left n hodd) ζ hζ.pow_eq_one
    rw [h2] at h1
    have h3 : p ≡ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val [MOD 2 ^ n] := by
      have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by positivity)
      rwa [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
    rw [map_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 h3, ZMod.natCast_zmod_val]
  have hcl : IsClosed ((decImage ℚ 2 A₀ : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
    ((isClosed_Dec (F := ℚ) A₀).isCompact.image (continuous_cycZ ℚ Ω 2)).isClosed
  obtain ⟨h0, hle⟩ := idxAdic (decImage ℚ 2 A₀) (cycZ ℚ Ω 2 g) p c hcl ⟨g, hg, rfl⟩ hu hc
  have e : (cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀ = (decImage ℚ 2 A₀).comap (cycZ ℚ Ω 2) := by
    rw [decImage, Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : (decImage ℚ 2 A₀).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  refine ⟨fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hrel0).trans ?_
  rwa [Subgroup.relIndex_top_right]
