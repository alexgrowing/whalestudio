import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants.Transport
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction.ExistsInfIdelesLocalResIdelesResFieldEqZeroOfInf
import GroundTheory.GlobalFields.CompletionAtPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal GroundTheory.LocalField ValuativeRel

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Valuation

variable {K F Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [Algebra K F] [ValuativeExtension K F] [Algebra.IsAlgebraic K F]
  [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

theorem algebraicValuativeRel_vle_algHom_iff (c : F →ₐ[K] Ω) (x y : F) :
    (letI := algebraicValuativeRel K Ω; c x ≤ᵥ c y) ↔ x ≤ᵥ y := by
  let := algebraicValuativeRel K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  rw [vle_iff_spectralNorm_le (K := K) (c x) (c y), vle_iff_spectralNorm_le (K := K) x y]
  let := normedField K
  change spectralNorm K Ω (c x) ≤ spectralNorm K Ω (c y) ↔ spectralNorm K F x ≤ spectralNorm K F y
  rw [spectralNorm, spectralNorm, spectralNorm, spectralNorm, minpoly.algHom_eq c c.injective,
    minpoly.algHom_eq c c.injective]

end Valuation

variable {K E : FiniteSubfield} [Fact (K ≤ E)]

section Finite

set_option maxHeartbeats 4000000 in

theorem brauerInvZOfIsSepClosure_idelesLocalRes_idelesResField (v : HeightOneSpectrum (𝓞 K.1))
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
    (y : cohomology (limitRep K) 2) :
    brauerInvZOfIsSepClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)
        (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
        ((idelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y)) =
      Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) •
        brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
          ((idelesLocalRes ι 2).hom y) := by
  have := finiteDimensional_adicCompletion_placesOver (E := E) (placeOfEmbedding ι E)
  let c := completionEmbedding ι E
  let L := c.fieldRange
  let : Algebra ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    c.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion K.1) _
  have : IsAlgClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) ≃ₐ[(placeOfEmbedding ι E).1.adicCompletion E.1]
      AlgebraicClosure (v.adicCompletion K.1) := IsAlgClosure.equiv _ _ _
  let : Algebra E.1 (AlgebraicClosure (v.adicCompletion K.1)) :=
    ((algebraMap ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
      (algebraMap E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1))).toAlgebra
  have : IsScalarTower E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure (v.adicCompletion K.1) :=
    { ι.toRingHom with commutes' := fun t => (completionEmbedding_algebraMap ι E t).symm }
  let ιE0 : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) :=
    (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ t, θ.toRingEquiv (ιE0 t) = ι t := fun t => θ.apply_symm_apply (ι t)
  have hL : ∀ l ∈ L, ∃ t : (placeOfEmbedding ι E).1.adicCompletion E.1,
      θ.toRingEquiv (algebraMap _ (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)) t) = l := by
    intro l hl
    obtain ⟨t, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨t, θ.commutes t⟩
  have : FiniteDimensional (v.adicCompletion K.1) L := LinearEquiv.finiteDimensional c.equivFieldRange.toLinearEquiv
  have : Algebra.IsIntegral L (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsIntegral.tower_top (v.adicCompletion K.1)
  have hfin : Module.finrank (v.adicCompletion K.1) L =
      Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) :=
    c.equivFieldRange.toLinearEquiv.finrank_eq.symm
  have hproj : ∀ z : IdeleLimit, θ.toRingEquiv (idelesProj ιE0 z : AlgebraicClosure _) =
      (idelesProj ι z : AlgebraicClosure (v.adicCompletion K.1)) :=
    idelesProj_eq_of_algebraMap (placeOfEmbedding ι E) ι ιE0 θ.toRingEquiv hι fun a => by
      change θ (algebraMap _ (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
        (algebraMap (v.adicCompletion K.1) _ a)) = _
      rw [θ.commutes]
      exact c.commutes a
  have key := cohomologyMapAlong_globalDecomp_idelesResField (v.adicCompletion K.1)
    ((placeOfEmbedding ι E).1.adicCompletion E.1) L θ.toRingEquiv hL ι ιE0 hι (idelesLocalMor ι) (idelesLocalMor ιE0)
    hproj 2 y
  have key' : (idelesLocalRes ιE0 2).hom ((idelesResField K E 2).hom y) =
      (cohomologyMapAlong (fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL)
        (continuous_fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL)
        (fieldConjUnitsMor (v.adicCompletion K.1) L θ.toRingEquiv hL) 2).hom
        ((unitsScalarsRes (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) L 2).hom
          ((idelesLocalRes ι 2).hom y)) := key
  rw [idelesLocalRes_eq_of_algHom ιE0 ιE, key']
  let := algebraicValuativeRel (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  let := algebraicTopology (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  have := algebraicTopology_isValuativeTopology (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  have := algebraicValuativeRel_valuativeExtension (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  let e : (placeOfEmbedding ι E).1.adicCompletion E.1 ≃+* L := c.equivFieldRange.toRingEquiv
  have hε : ∀ x, θ.toRingEquiv (algebraMap ((placeOfEmbedding ι E).1.adicCompletion E.1)
      (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)) x) =
      algebraMap L (AlgebraicClosure (v.adicCompletion K.1)) (e x) := fun x => θ.commutes x
  have he : ∀ x y : (placeOfEmbedding ι E).1.adicCompletion E.1, e x ≤ᵥ e y ↔ x ≤ᵥ y := fun x y => by
    rw [← IntermediateField.coe_vle_coe_iff]
    exact algebraicValuativeRel_vle_algHom_iff c x y
  have hρ : ∀ (σ : Gal(AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) /
      (placeOfEmbedding ι E).1.adicCompletion E.1)) (x : AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)),
      fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL σ (θ.toRingEquiv x) = θ.toRingEquiv (σ x) :=
    fun σ x => by rw [fieldConjHom_apply, RingEquiv.symm_apply_apply]
  rw [brauerInvZOfIsSepClosure_cohomologyMapAlong_transport e θ.toRingEquiv hε _
    (continuous_fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL) hρ _ (fun _ => rfl) he,
    brauerInvZOfIsSepClosure_unitsScalarsRes, hfin]

end Finite

end

end GroundTheory.ProfCoh
