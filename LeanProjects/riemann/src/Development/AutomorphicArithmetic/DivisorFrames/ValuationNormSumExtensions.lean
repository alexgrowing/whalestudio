import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OrdFracEqValuationInvOfIsLocalization
open IsLocalRing NumberField IsDedekindDomain GlobalTheory.ValCount
open scoped Classical

section SlopeTestRemainingChoices

variable {K L : Type} [Field K] [Field L] [Algebra K L] (W : ValuationSubring K)
  [IsDiscreteValuationRing W] {S : Type} [CommRing S] [IsDedekindDomain S] [Algebra W S]
  [Algebra S L] [IsScalarTower W S L] [IsFractionRing S L] [Module.Finite W S]

private theorem vc_dvr (P : HeightOneSpectrum S) :
    IsDiscreteValuationRing (P.valuationSubringAtPrime L) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S P.ne_bot _

private theorem vc_mem_nonunits (P : HeightOneSpectrum S) (s : S) :
    algebraMap S L s ∈ (P.valuationSubringAtPrime L).nonunits ↔ s ∈ P.asIdeal := by
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (P.valuationSubringAtPrime L) P.asIdeal s]
  exact ValuationSubring.coe_mem_nonunits_iff (a := algebraMap S (P.valuationSubringAtPrime L) s)

private theorem vc_inj : Function.Injective
    (fun P : HeightOneSpectrum S => P.valuationSubringAtPrime L) := by
  intro P Q h
  ext s
  have h' : P.valuationSubringAtPrime L = Q.valuationSubringAtPrime L := h
  rw [← vc_mem_nonunits (L := L), ← vc_mem_nonunits (L := L), h']

private theorem vc_comap (P : HeightOneSpectrum S) :
    (P.valuationSubringAtPrime L).comap (algebraMap K L) = W := by
  have := GlobalTheory.ExtField.faithfulSMul_of_tower W K S L
  symm
  apply ValuationSubring.eq_of_le_of_ne_top
  · intro a ha
    have : algebraMap K L a = algebraMap S L (algebraMap W S ⟨a, ha⟩) := by
      rw [← IsScalarTower.algebraMap_apply]; rfl
    rw [ValuationSubring.mem_comap, this]
    exact (algebraMap S (P.valuationSubringAtPrime L) _).2
  · intro h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have h1 : P.asIdeal.under W = maximalIdeal W := by
      have := P.isMaximal
      exact IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under W P.asIdeal)
    have h2 : algebraMap W S ϖ ∈ P.asIdeal := by
      have : ϖ ∈ P.asIdeal.under W := h1 ▸ hϖ.not_isUnit
      exact this
    rw [← vc_mem_nonunits (L := L), ← IsScalarTower.algebraMap_apply] at h2
    have h3 : (ϖ : K) ∈ ((P.valuationSubringAtPrime L).comap (algebraMap K L)).nonunits :=
      (mem_nonunits_comap _ _ _).2 h2
    rw [h, ValuationSubring.mem_nonunits_iff_or] at h3
    rcases h3 with h3 | h3
    · exact hϖ.ne_zero (Subtype.ext h3)
    · exact h3 (ValuationSubring.mem_top _)

private theorem vc_surj (V : ValuationSubring L) (hV : V.comap (algebraMap K L) = W) :
    ∃ P : HeightOneSpectrum S, P.valuationSubringAtPrime L = V := by
  have hWV : ∀ a : W, algebraMap W L a ∈ V := fun a => by
    have : (a : K) ∈ V.comap (algebraMap K L) := hV ▸ a.2
    exact this
  have hS : ∀ s : S, algebraMap S L s ∈ V := by
    intro s
    letI : Algebra W V := ((algebraMap W L).codRestrict V hWV).toAlgebra
    haveI : IsScalarTower W V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h1 : IsIntegral W (algebraMap S L s) := (Algebra.IsIntegral.isIntegral s).algebraMap
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (h1.tower_top (A := V))
    rw [← hy]; exact y.2
  let f : S →+* V := (algebraMap S L).codRestrict V hS
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have h0 : algebraMap K L ϖ ≠ 0 := by
    rw [map_ne_zero]; exact fun h => hϖ.ne_zero (Subtype.ext h)
  have h1 : algebraMap K L ϖ ∈ V.nonunits := by
    rw [← mem_nonunits_comap, hV]
    exact ValuationSubring.coe_mem_nonunits_iff.2 hϖ.not_isUnit
  have h2 : algebraMap K L ϖ = algebraMap S L (algebraMap W S ϖ) := by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hne : (maximalIdeal V).comap f ≠ ⊥ := by
    intro h
    have : algebraMap W S ϖ ∈ (maximalIdeal V).comap f := by
      rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
      rw [h2] at h1
      exact h1
    rw [h, Ideal.mem_bot] at this
    rw [h2, this, map_zero] at h0
    exact h0 rfl
  refine ⟨⟨(maximalIdeal V).comap f, inferInstance, hne⟩, ?_⟩
  apply ValuationSubring.eq_of_le_of_ne_top
  · rintro x ⟨a, s, hs, rfl⟩
    refine V.mul_mem _ _ (hS a) ?_
    have h3 : algebraMap S L s ∉ V.nonunits := fun h =>
      hs ((ValuationSubring.coe_mem_nonunits_iff (a := f s)).1 h)
    rw [ValuationSubring.mem_nonunits_iff_or] at h3
    push Not at h3
    exact h3.2
  · rintro rfl
    rw [ValuationSubring.mem_nonunits_iff_or] at h1
    rcases h1 with h3 | h3
    · exact h0 h3
    · exact h3 (ValuationSubring.mem_top _)

private theorem vc_vdeg (P : HeightOneSpectrum S) :
    vdeg (algebraMap K L) (P.valuationSubringAtPrime L) = P.asIdeal.inertiaDeg W := by
  have hc := vc_comap W P (L := L)
  have := P.isMaximal
  have h1 : P.asIdeal.under W = maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under W P.asIdeal)
  have : P.asIdeal.LiesOver (maximalIdeal W) := ⟨h1.symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal W) P.asIdeal]
  let e : W ≃+* (P.valuationSubringAtPrime L).comap (algebraMap K L) :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hc.symm)
  unfold vdeg
  letI := (ResidueField.map (vres (algebraMap K L) (P.valuationSubringAtPrime L))).toAlgebra
  symm
  refine Algebra.finrank_eq_of_equiv_equiv (ResidueField.mapEquiv e)
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (P.valuationSubringAtPrime L)) ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  have h2 : vres (algebraMap K L) (P.valuationSubringAtPrime L) (e a) =
      algebraMap S (P.valuationSubringAtPrime L) (algebraMap W S a) :=
    Subtype.ext (IsScalarTower.algebraMap_apply W S L a)
  refine Eq.trans ?_ (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk P.asIdeal
    (P.valuationSubringAtPrime L) (algebraMap W S a)).symm
  rw [← h2]
  rfl

end SlopeTestRemainingChoices

theorem UpperTheory.valuation_norm_sum_extensions :
    ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L), φ.Finite → ∀ (W : ValuationSubring K) [IsDiscreteValuationRing W], {V : ValuationSubring L | V.comap φ = W}.Finite ∧ (∀ V : ValuationSubring L, V.comap φ = W → IsDiscreteValuationRing V) ∧ ∀ x : L, x ≠ 0 → vord W (rnorm φ x) = ∑ᶠ V : ValuationSubring L, if V.comap φ = W then vord V x * (vdeg φ V : ℤ) else 0 := by
  intro K L _ _ _ φ hφ W _
  letI := φ.toAlgebra
  haveI : FiniteDimensional K L := hφ
  let S := integralClosure W L
  haveI : Module.Finite W S := IsIntegralClosure.finite W K L S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain W K L S
  haveI : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension W K L S
  haveI : Finite (HeightOneSpectrum S) := GlobalTheory.ExtField.finite_heightOneSpectrum W S
  have hφ' : φ = algebraMap K L := rfl
  have hset : {V : ValuationSubring L | V.comap φ = W} =
      Set.range (fun P : HeightOneSpectrum S => P.valuationSubringAtPrime L) := by
    ext V
    exact ⟨fun h => vc_surj W V h, by rintro ⟨P, rfl⟩; exact vc_comap W P⟩
  refine ⟨hset ▸ Set.finite_range _, fun V hV => ?_, fun x hx => ?_⟩
  · obtain ⟨P, rfl⟩ := vc_surj (S := S) W V hV
    exact vc_dvr P
  · letI := Fintype.ofFinite (HeightOneSpectrum S)
    have h1 : (∑ᶠ V : ValuationSubring L, if V.comap φ = W then vord V x * (vdeg φ V : ℤ) else 0) =
        ∑ᶠ V ∈ {V : ValuationSubring L | V.comap φ = W}, vord V x * (vdeg φ V : ℤ) := by
      refine finsum_congr fun V => ?_
      rw [finsum_eq_if]; rfl
    rw [h1, hset, finsum_mem_range vc_inj, finsum_eq_sum_of_fintype, vord_eq]
    refine (GlobalTheory.ExtField.log_ordFrac_norm_eq_sum W K S hx).trans (Finset.sum_congr rfl fun P _ => ?_)
    haveI := vc_dvr (L := L) P
    rw [hφ', vc_vdeg W P, vord_eq, GlobalTheory.ExtField.log_ordFrac_eq_neg_log_valuation P, mul_comm]
