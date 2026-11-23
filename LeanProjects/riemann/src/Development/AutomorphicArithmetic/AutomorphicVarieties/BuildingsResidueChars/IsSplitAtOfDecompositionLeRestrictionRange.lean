import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)
open scoped Pointwise

section SlopeTestRemainingChoices

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
  [IsScalarTower F E Ω]

private theorem place_conj {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v := fun x => by
  have hm : ∀ x, x ∈ t⁻¹ • A ↔ t x ∈ A := fun x => ValuationSubring.mem_inv_pointwise_smul_iff
  have hv : ∀ y, (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hm, hm, map_inv₀, map_eq_zero_iff _ t.injective]
  rw [hv, AlgEquiv.commutes]
  exact h x

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 E), IsPlaceOver A w ∧ w.under (𝓞 F) = v := by
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap E Ω (x : E)) := (x.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 E →+* A := ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A hint
  let P : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 F) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F E Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

end SlopeTestRemainingChoices

theorem UpperTheory.isSplitAt_of_decomposition_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Dec (F := Lp L) A ≤ (resP L Ω).range → ∀ w : Plc L, w.under (𝓞 (Lp L)) = v → IsSplitAt w := by
  intro L Ω _ _ _ _ _ _ A v hA hD w hw
  by_contra hs
  have huniq : ∀ u : Plc L, u.under (𝓞 (Lp L)) = v → u = w := fun u hu => by
    by_contra h
    exact hs ⟨u, h, hu.trans hw.symm⟩
  haveI : Normal (Lp L) Ω := IsAlgClosure.normal _ _
  let t : G (Lp L) Ω := (IsCMField.complexConj L).liftNormal Ω
  have ht : ∀ y : L, t (algebraMap L Ω y) = algebraMap L Ω (IsCMField.complexConj L y) := fun y =>
    AlgEquiv.liftNormal_commutes _ Ω y
  obtain ⟨u, hu, hu'⟩ := place_between (E := L) hA
  obtain ⟨u', hu1, hu1'⟩ := place_between (E := L) (place_conj hA t)
  rw [huniq u hu'] at hu
  rw [huniq u' hu1'] at hu1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := L) hu hu1
  have hg' : resP L Ω g • A = t⁻¹ • A := hg
  have hm : t * resP L Ω g ∈ Dec (F := Lp L) A := by
    show (t * resP L Ω g) • A = A
    rw [mul_smul, hg', smul_inv_smul]
  obtain ⟨k, hk⟩ := (Subgroup.mul_mem_cancel_right _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)).1 (hD hm)
  apply IsCMField.complexConj_ne_one L
  ext y
  apply (algebraMap L Ω).injective
  rw [← ht, ← hk]
  exact k.commutes y
