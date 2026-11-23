import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.CycDec

theorem exists_unit_infinite_order (l : ℕ) [Fact l.Prime] :
    ∃ u : ℤ_[l]ˣ, ∀ n : ℤ, n ≠ 0 → u ^ n ≠ 1 := by
  have hl : l.Prime := Fact.out
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, fun n hn h => ?_⟩
  have h1 : u ^ n.natAbs = 1 := by
    rcases Int.natAbs_eq n with e | e
    · rw [← zpow_natCast, ← e, h]
    · rw [e, zpow_neg, inv_eq_one, zpow_natCast] at h
      exact h
  have h2 : (((1 + l) ^ n.natAbs : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    push_cast
    rw [← hu, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have h3 := Nat.cast_injective h2
  rw [pow_eq_one_iff] at h3
  rcases h3 with h3 | h3
  · exact hl.ne_zero (by omega)
  · exact hn (Int.natAbs_eq_zero.1 h3)

theorem exists_mem_Dec_cycZ_zpow_ne_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F))
    (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∀ n : ℤ, n ≠ 0 →
    ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  intro F Ω _ _ _ _ _ l _ v A hl hA n hn
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Dec (F := ℚ) A := (Dec (F := ℚ) A).pow_mem (Ine_le_Dec A hσ) N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  refine ⟨g, hD, ?_⟩
  rw [hc, map_pow, hσu, ← zpow_natCast, ← zpow_mul]
  exact hu _ (mul_ne_zero (by exact_mod_cast hN.ne') hn)

end GlobalTheory.CycDec
