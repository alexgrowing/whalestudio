import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

theorem odd_or_tc_base_pf
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1) : Odd ℓ ∨ IsTotallyComplex K.1 := by
  have hℓ : ℓ.Prime := Fact.out
  by_cases h2 : ℓ = 2
  · right
    subst h2
    have hTC : IsTotallyComplex L.1 := hK.resolve_left (by simp)
    haveI : IsGalois K.1 L.1 := ⟨⟩
    refine ⟨fun v => ?_⟩
    by_contra hv
    rw [InfinitePlace.not_isComplex_iff_isReal] at hv
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K.1) (K := L.1) v
    have hw : w.IsComplex := hTC.isComplex w
    have hram : ¬ InfinitePlace.IsUnramified K.1 w :=
      InfinitePlace.not_isUnramified_iff.2 ⟨hw, hv⟩
    have hcard := InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.1 hram
    have hdvd : 2 ∣ Nat.card (L.1 ≃ₐ[K.1] L.1) :=
      hcard ▸ Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) w)
    have hidx : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index =
        Nat.card (L.1 ≃ₐ[K.1] L.1) := by
      rw [Subgroup.index]
      exact Nat.card_congr (gsQuotientGalEquiv hL).toEquiv
    rw [hidx] at hcop
    have := Nat.Coprime.coprime_dvd_left hdvd hcop
    norm_num at this
  · left
    exact hℓ.odd_of_ne_two h2

end PositivityTheory.Lit1.GEN.X
