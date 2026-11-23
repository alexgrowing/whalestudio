import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TameDesign
open scoped Pointwise

private theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h := A.valuation.map_one_add_of_lt (hσ y hy)
    rw [add_sub_cancel, map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h
    exact h
  refine ⟨?_, fun x hx => ?_⟩
  · show σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hσ x hx0)

section General

variable {Γ R : Type} [Group Γ] [CommRing R]

private theorem mem_ker_char_iff (J : Ideal R) (χ : Γ →* Rˣ) (g : Γ) :
    g ∈ ((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker ↔ ((χ g : Rˣ) : R) - 1 ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
  rfl

private theorem isOpen_ker_char [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (χ : Γ →* Rˣ)
    (hχ : Continuous fun g => ((χ g : Rˣ) : R)) :
    IsOpen (((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker : Set Γ) := by
  have : (((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker : Set Γ) =
      (fun g => ((χ g : Rˣ) : R) - 1) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_char_iff, Set.mem_preimage]
  rw [this]
  exact hJ.preimage (hχ.sub continuous_const)

end General

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

omit [TopologicalSpace R] [IsTopologicalRing R] in
private theorem eq_zero_of_mem_pow (x : R) (h : ∀ m, x ∈ IsLocalRing.maximalIdeal R ^ (m + 1)) : x = 0 := by
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Ideal.mem_iInf]
  exact fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (h m)

private theorem char_eq_one_of_wild (hR : IsAdic (IsLocalRing.maximalIdeal R)) (hA : IsPlaceOver A v) (n : ℕ)
    (hv : ((n : ℕ) : 𝓞 E) ∉ v.asIdeal) (χ : Formalism.ConjugateSelfDual.G E Ω →* Rˣ) (hχ : Continuous fun g => ((χ g : Rˣ) : R))
    (σ : Formalism.ConjugateSelfDual.G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (h1 : χ σ ^ n = 1) : χ σ = 1 := by
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  refine eq_zero_of_mem_pow _ fun m => ?_
  rw [← mem_ker_char_iff]
  refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal E Ω A v hA _ inferInstance
    (isOpen_ker_char _ ((isAdic_iff.mp hR).1 _) χ hχ) σ n hv hσ ?_
  rw [mem_ker_char_iff, map_pow, h1]
  simp

end Wild

theorem firstLocalChar_wild_eq_one_away_from_l (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hvl : v ∉ placesOver D.host.E (D.nd.l i)) (σ : GE D.nd) (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 v)) :
    D.nd.chi i 1 σ = 1 := by
  have hA : IsPlaceOver (D.nd.plOm.1 v) v := D.nd.plOm.2 v
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v) := wild_mem_Ine hσ
  have hvl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by rwa [D.ntw.twOf_l]

  have hψ : D.ntw.psiL i σ = 1 := by
    obtain ⟨n, hn⟩ := D.ntw.psiL_ord i σ
    have hmem := GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ (D.nd.plOm.1 v) v hA (D.ntw.psiL i).ker
      inferInstance (D.ntw.psiL_open i) σ (D.nd.l i ^ n) ?_ hσ (by rw [MonoidHom.mem_ker, map_pow, hn])
    · exact hmem
    · intro h
      apply hvl
      have hp : (D.nd.l i).Prime := Fact.out
      exact v.isPrime.mem_of_pow_mem n (by simpa using h)

  have hc : D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) σ = 1 := by
    by_cases hpD : v ∈ D.ntw.pD (D.ntw.twOf i)
    · have h15 := D.ntw.delta_15 (D.ntw.twOf i) v hpD _ hA
      have hd : D.ntw.delta (D.ntw.twOf i) σ ^ 15 = 1 := by
        have h := pow_card_eq_one'
          (G := (Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.ntw.delta (D.ntw.twOf i)))
          (x := ⟨_, σ, hI, rfl⟩)
        rw [h15] at h
        exact congrArg Subtype.val h
      have h15v : ((15 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
        intro h
        have hN := D.ntw.delta_tame (D.ntw.twOf i) v hpD
        have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := Ideal.absNorm_mem _
        have e : Ideal.absNorm v.asIdeal = 15 * (Ideal.absNorm v.asIdeal / 15) + 1 := by omega
        rw [e] at hm
        push_cast at hm
        have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
          have := v.asIdeal.sub_mem hm (v.asIdeal.mul_mem_right (((Ideal.absNorm v.asIdeal / 15 : ℕ)) : 𝓞 D.host.E) (by simpa using h))
          simpa using this
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      refine char_eq_one_of_wild (D.ntw.twistBaseCoefficientRing_isAdic _) hA 15 h15v _
        (D.ntw.twistCharacterFamily_continuous _ _ _) σ hσ ?_
      rw [D.ntw.twistCharacterFamily_at_auxiliaryPlaces _ _ _ v hpD _ hA σ hI]
      split_ifs
      · exact hd
      · rw [inv_pow, hd, inv_one]
    · by_cases hg : ∃ k, v ∈ placesOver D.host.E (D.host.g k)
      · obtain ⟨k, hvg⟩ := hg
        have hg1 : ((D.host.g k - 1 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun hm => by
          refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
          have := v.asIdeal.sub_mem hvg hm
          rwa [Nat.cast_sub (D.host.g_prime k).one_le, Nat.cast_one, sub_sub_cancel] at this
        exact char_eq_one_of_wild (D.ntw.twistBaseCoefficientRing_isAdic _) hA _ hg1 _
          (D.ntw.twistCharacterFamily_continuous _ _ _) σ hσ (D.ntw.twistCharacterFamily_tame _ _ _ k v hvg hvl' _ hA σ hI)
      · push_neg at hg
        exact D.ntw.twistCharacterFamily_unramified _ _ _ v hvl' hg hpD _ hA σ hI
  rw [D.ntw.chi_tw i]
  simp [hψ, hc]

theorem main : ∀ (D : D7) (i : D.nd.Loc), TameCharacterConditions D i ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  intro D i
  have hc : TameCharacterConditions D i := by
    refine ⟨fun v hv σ hσ => GlobalTheory.TameDesign.firstLocalChar_wild_eq_one_away_from_l D i v ?_ σ hσ, Formalism.MainNotions.SumRepresentations.Del_holds D i⟩
    rcases hv with hQ | ⟨hS, -⟩
    · exact D.nd.SQ_l i v (Or.inr hQ)
    · exact D.nd.SQ_l i v (Or.inl hS)
  exact ⟨hc, galois_condition_five_extra_of D i hc⟩

end GlobalTheory.TameDesign
