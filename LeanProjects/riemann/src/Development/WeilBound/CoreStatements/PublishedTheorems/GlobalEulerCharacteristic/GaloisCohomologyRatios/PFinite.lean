import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.ModuleFiniteHomRep

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

omit [Normal K.1 L.1] in
theorem module_finite_S_units [Finite S] : Module.Finite ℤ (AA hL 0) := by
  have : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := finite_placesOver (L := L.1) (S := S)
  exact Module.Finite.equiv (gsH0SUnitsEquiv hL).symm.toIntLinearEquiv

omit [Normal K.1 L.1] in
theorem finite_H1_S_units : Finite (AA hL 1) := finite_gsH1SUnits hL

theorem finite_modN_AA [Finite S] (i : ℕ) (hi : i ≤ 1) : Finite (ModN (AA hL i) ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  interval_cases i
  · have := module_finite_S_units hL
    exact finite_modN_of_moduleFinite ℓ
  · have := finite_H1_S_units hL
    exact Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)

theorem finite_torsN_AA [Finite S] (i : ℕ) (hi : i ≤ 1) : Finite (TorsN (AA hL i) ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  interval_cases i
  · have := module_finite_S_units hL
    exact finite_torsN_of_moduleFinite ℓ
  · have := finite_H1_S_units hL
    exact Subtype.finite

theorem card_gal_eq_index : Nat.card (L.1 ≃ₐ[K.1] L.1) =
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index := by
  rw [Subgroup.index]
  exact (Nat.card_congr (gsQuotientGalEquiv hL).toEquiv).symm

end PositivityTheory.Lit1.GEN.X
