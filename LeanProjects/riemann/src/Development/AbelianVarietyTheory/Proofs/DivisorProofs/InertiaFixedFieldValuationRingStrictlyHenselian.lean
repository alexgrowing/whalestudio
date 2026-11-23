import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldMaximalIdealDvdUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemDivUniformizerPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingFixedFieldInertiaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaFixedSH

theorem vs_inv_mem_of_not_mem_nonunits {F : Type} [Field F] (A : ValuationSubring F) {x : F} (hx : x ∈ A)
    (hn : x ∉ A.nonunits) : x ≠ 0 ∧ x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt] at hn
  have h1 : A.valuation x = 1 := le_antisymm ((A.valuation_le_one_iff x).2 hx) hn
  refine ⟨fun h => by simp [h] at h1, ?_⟩
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem inertiaFixed_strictlyHenselian : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → GlobalTheory.SS.SH (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ∧ ∃ f : R →+* V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω), (∀ r : R, ((f r : IntermediateField.fixedField (inertia K V)) : Ω) = algebraMap K Ω (algebraMap R K r)) ∧ ∀ π : R, Irreducible π → Irreducible (f π) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  have hc : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := hV ▸ ⟨r, rfl⟩
    exact this
  have hinv : ∀ π : R, Irreducible π → (algebraMap K Ω (algebraMap R K π))⁻¹ ∉ V := by
    intro π hπ h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω _ ∈ V
      rwa [map_inv₀]
    rw [hV] at h'
    obtain ⟨s, hs⟩ := h'
    have hπ0 : algebraMap R K π ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨s, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hs, map_one, mul_inv_cancel₀ hπ0]
  have hc0 : ∀ π : R, Irreducible π → algebraMap K Ω (algebraMap R K π) ≠ 0 := by
    intro π hπ h
    apply hinv π hπ
    rw [h, inv_zero]; exact V.zero_mem
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set V' := V.comap (algebraMap K' Ω) with hV'
  have memV' : ∀ y : K', y ∈ V' ↔ (y : Ω) ∈ V := fun y => ValuationSubring.mem_comap
  let f : R →+* V' := ((algebraMap K K').comp (algebraMap R K)).codRestrict V' (fun r => by
      rw [memV']; simpa using hc r)
  have hf : ∀ r : R, ((f r : K') : Ω) = algebraMap K Ω (algebraMap R K r) := fun r => by simp [f]
  have unitV' : ∀ a : V', ((a : K') : Ω) ∉ V.nonunits → IsUnit a := by
    intro a ha
    obtain ⟨h0, hi⟩ := vs_inv_mem_of_not_mem_nonunits V ((memV' a).1 a.2) ha
    have hmem : (a : K')⁻¹ ∈ V' := by rw [memV']; simpa using hi
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv, OneMemClass.coe_one,
      IntermediateField.coe_one]
    exact mul_inv_cancel₀ h0
  have hfπ : ∀ π : R, Irreducible π → Irreducible (f π) := by
    intro π hπ
    refine irreducible_iff.2 ⟨fun hu => hinv π hπ ?_, fun a b hab => ?_⟩
    · obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hb' : ((f π : K') : Ω) * ((b : K') : Ω) = 1 := by
        have := congrArg (fun z : V' => ((z : K') : Ω)) hb
        simpa using this
      rw [hf] at hb'
      rw [inv_eq_of_mul_eq_one_right hb']
      exact (memV' b).1 b.2
    · by_contra hne
      push_neg at hne
      have ha : ((a : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.1 (unitV' a h)
      have hb : ((b : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.2 (unitV' b h)
      have h1 := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ (a : K').2 ha
      have h2 := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ (b : K').2 hb
      have hab' : algebraMap K Ω (algebraMap R K π) = ((a : K') : Ω) * ((b : K') : Ω) := by
        rw [← hf, hab]; simp
      apply hinv π hπ
      have h0 := hc0 π hπ
      convert mul_mem h1 h2 using 1
      rw [div_mul_div_comm, ← hab']
      field_simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hdvr : IsDiscreteValuationRing V' := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨f π, hfπ π hπ, fun {x} hx => ?_⟩
    have hx0 : ((x : K') : Ω) ≠ 0 := by
      intro h; apply hx; apply Subtype.ext; apply Subtype.ext; simpa using h
    classical
    have hex := GlobalTheory.T.not_mem_div_uniformizer_pow_alt R K Ω V hV π hπ _ hx0
    have hn := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by
      intro h; rw [h] at hn; apply hn; simpa using (memV' x).1 x.2
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hmin : ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m ∈ V := by
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      simpa using this
    set y : K' := (x : K') / (algebraMap K K' (algebraMap R K π)) ^ m with hy
    have hyΩ : (y : Ω) = ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m := by simp [y]
    have hyV' : y ∈ V' := by rw [memV', hyΩ]; exact hmin
    have hyU : (y : Ω) ∉ V.nonunits := by
      intro hyn
      have := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ y.2 hyn
      apply hn
      rw [hm, hyΩ] at *
      convert this using 1
      rw [pow_succ, div_div]
    refine ⟨m, (unitV' ⟨y, hyV'⟩ hyU).unit, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    simp only [IsUnit.unit_spec, MulMemClass.coe_mul, IntermediateField.coe_mul, SubmonoidClass.coe_pow,
      IntermediateField.coe_pow]
    rw [hf, hyΩ]
    field_simp [pow_ne_zero m (hc0 π hπ)]
  exact ⟨⟨hdvr, GlobalTheory.T.henselianLocalRing_fixedField_inertia_alt R K Ω V hV, GlobalTheory.T.residueField_inertiaFixed_isAlgClosed_alt R K Ω V hV, inferInstance⟩, f, hf, hfπ⟩

end GlobalTheory.InertiaFixedSH
