import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialLocal
import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
import GroundTheory.LocalFields.MaximalUnramifiedIntegers
import GroundTheory.LocalFields.TameExtension
import GroundTheory.LocalFields.LocalArtinTransport
import GroundTheory.LocalFields.LocalArtinMap
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits

namespace GroundTheory.Global

open IsDedekindDomain NumberField ValuativeRel GroundTheory.LocalField SemiLocal
open scoped Pointwise

noncomputable section

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra k M] [ValuativeExtension k M] [FiniteDimensional k M]
  [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)]

theorem normResidueSymbol_integer_sub_pow_mem (hM : ramificationIndex k M = 1) {π : kˣ}
    (hπ : ord (π : k) = 1) (z : 𝒪[M]) :
    integerAlgEquiv k M (normResidueSymbol k M π) z - z ^ Nat.card 𝓀[k] ∈ 𝓂[M] := by
  let ι : M →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let E : IntermediateField k (SeparableClosure k) := ι.fieldRange
  have : FiniteDimensional k E := finiteDimensional_fieldRange ι
  let j : M ≃ₐ[k] E := ι.equivFieldRange
  have hj : ∀ x y : M, j.toRingEquiv x ≤ᵥ j.toRingEquiv y ↔ x ≤ᵥ y :=
    vle_map_iff j.toAlgHom

  have hE : ramificationIndex k E = 1 := by
    have h1 := ord_algebraMap (K := k) (L := M) (π : k)
    have h2 := ord_algebraMap (K := k) (L := E) (π : k)
    have h3 := ord_apply_of_vle j.toRingEquiv hj (Units.map (algebraMap k M).toMonoidHom π)
    have h4 : j.toRingEquiv (algebraMap k M (π : k)) = algebraMap k E (π : k) := j.commutes _
    change ord (j.toRingEquiv (algebraMap k M (π : k))) = ord (algebraMap k M (π : k)) at h3
    rw [h4, h2, h1, hπ, hM] at h3
    simpa using h3
  have hle : E ≤ maximalUnramifiedExtension k (SeparableClosure k) :=
    ((isUnramifiedSubextension_iff' E).2 hE).le_maximalUnramifiedExtension
  have hmem : ∀ x : M, ι x ∈ maximalUnramifiedExtension k (SeparableClosure k) :=
    fun x ↦ hle ⟨x, rfl⟩

  have key : ι (normResidueSymbol k M π z) =
      (maximalUnramifiedExtensionFrobenius k (SeparableClosure k) ⟨ι z, hmem z⟩ :
        SeparableClosure k) := by
    rw [normResidueSymbol_apply_eq_localArtinMap ι π (z : M)]
    exact localArtinMap_uniformizer_apply hπ (hmem z)

  have hval : ∀ x : M, valuation (SeparableClosure k) (ι x) ≤ 1 ↔ x ∈ 𝒪[M] := fun x ↦
    (mem_integer_intermediateField_iff E (j x)).symm.trans (apply_mem_integer_iff j.toRingEquiv hj x)
  have hlt : ∀ x : 𝒪[M], x ∈ 𝓂[M] ↔ valuation (SeparableClosure k) (ι (x : M)) < 1 := fun x ↦ by
    change x ∈ 𝓂[M] ↔ valuation (SeparableClosure k)
      (((integerEquivOfVle j.toRingEquiv hj x : E) : SeparableClosure k)) < 1
    rw [← mem_maximalIdeal_intermediateField_iff E (integerEquivOfVle j.toRingEquiv hj x),
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]
  let y : 𝒪[maximalUnramifiedExtension k (SeparableClosure k)] :=
    ⟨⟨ι z, hmem z⟩, (mem_integer_intermediateField_iff _ _).2 ((hval z).2 z.2)⟩
  have hf := frobenius_integer_sub_pow_mem_maximalIdeal (K := k) (Ω := SeparableClosure k) y
  rw [mem_maximalIdeal_intermediateField_iff] at hf
  rw [hlt]
  convert hf using 2
  simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, map_sub, map_pow,
    coe_integerAlgEquiv_apply, coe_integerAlgEquivOfIsAlgebraic_apply]
  rw [key]

end Local

section Global

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

theorem localSymbol_eq_arithFrobAt (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    {π : (v.adicCompletion K)ˣ} (hπ : ord (π : v.adicCompletion K) = 1) :
    localSymbol L v π = arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal := by
  let w' : PlacesOver L v := ⟨w, inferInstance⟩
  have := isMulCommutative_gal_adicCompletion L v w'
  have hM : ramificationIndex (v.adicCompletion K) (w.adicCompletion L) = 1 :=
    (ramificationIdx_integer v w).trans he
  have h := eq_decompositionToLocal_arithFrobAt v w he _
    (normResidueSymbol_integer_sub_pow_mem hM hπ)
  rw [localSymbol_eq_symbolAt L v w']
  change (((decompositionMulEquiv v w).symm
    (normResidueSymbol (v.adicCompletion K) (w.adicCompletion L) π) :
      MulAction.stabilizer Gal(L/K) w.asIdeal) : Gal(L/K)) = _
  rw [h, ← decompositionMulEquiv_apply, MulEquiv.symm_apply_apply]
  rfl

theorem ideleSymbol_finiteEmbedding_eq_arithFrobAt (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    {π : (v.adicCompletion K)ˣ} (hπ : ord (π : v.adicCompletion K) = 1) :
    ideleSymbol K L (IdeleGroup.finiteEmbedding v π) = arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal := by
  rw [ideleSymbol_finiteEmbedding, localSymbol_eq_arithFrobAt v w he hπ]

end Global

end

end GroundTheory.Global
