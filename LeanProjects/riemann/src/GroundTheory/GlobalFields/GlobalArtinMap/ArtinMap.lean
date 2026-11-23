import Mathlib
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialLocal
import GroundTheory.LocalFields.MaximalAbelianExtension

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup GroundTheory.LocalField SemiLocal

noncomputable section

universe u

section Restrict

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem reciprocityMap_apply_of_le {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [IsAbelianGalois K L] [FiniteDimensional K L'] [IsAbelianGalois K L'] (h : L ≤ L')
    (c : IdeleClassGroup K) (l : L) :
    ((reciprocityMap K L' c ⟨l, h l.2⟩ : L') : Ω) = ((reciprocityMap K L c l : L) : Ω) := by
  let _ : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [reciprocityMap_mk, reciprocityMap_mk, ← restrictNormal_ideleSymbol (L := L) (M := L')]
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes (ideleSymbol K L' x) L l).symm

variable [IsGalois K Ω]

omit [NumberField K] in

theorem restrictAb_eq_of_le {L L' : IntermediateField K Ω} [Normal K L] [Normal K L']
    (hL' : L' ≤ maximalAbelianExtension K Ω) (h : L ≤ L')
    {σ τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω}
    (hστ : restrictAb L' hL' σ = restrictAb L' hL' τ) :
    restrictAb L (h.trans hL') σ = restrictAb L (h.trans hL') τ := by
  ext l
  have e := congrArg (fun ρ : L' ≃ₐ[K] L' ↦ ((ρ ⟨l, h l.2⟩ : L') : Ω)) hστ
  simp only [restrictAb_apply] at e ⊢
  exact e

theorem restrictAb_eq_reciprocityMap_of_le {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [IsAbelianGalois K L] [FiniteDimensional K L'] [IsAbelianGalois K L'] (h : L ≤ L')
    {c : IdeleClassGroup K} {τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω}
    (hτ : restrictAb L' (le_maximalAbelianExtension L') τ = reciprocityMap K L' c) :
    restrictAb L (le_maximalAbelianExtension L) τ = reciprocityMap K L c := by
  ext l
  have e := congrArg (fun ρ : L' ≃ₐ[K] L' ↦ ((ρ ⟨l, h l.2⟩ : L') : Ω)) hτ
  simp only [restrictAb_apply] at e ⊢
  rw [e, reciprocityMap_apply_of_le h]

end Restrict

section ArtinMap

variable (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω] [Algebra K Ω] [IsGalois K Ω]

instance nonempty_finiteAbelianExtensions : Nonempty (finiteAbelianExtensions K Ω) :=
  ⟨⟨⊥, inferInstance, inferInstance⟩⟩

variable {K Ω} in

def fiberOver (c : IdeleClassGroup K) (L : finiteAbelianExtensions K Ω) :
    Set (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  haveI := L.2.1
  haveI := L.2.2
  {τ | restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ =
    reciprocityMap K (L : IntermediateField K Ω) c}

theorem exists_restrictAb_eq_reciprocityMap (c : IdeleClassGroup K) :
    ∃ τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω,
      ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        restrictAb L (le_maximalAbelianExtension L) τ = reciprocityMap K L c := by
  have hcl : ∀ L : finiteAbelianExtensions K Ω, IsClosed (fiberOver c L) := fun L ↦ by
    have := L.2.1
    have := L.2.2
    exact isClosed_eq (continuous_restrictAb _ _) continuous_const
  have hne : ∀ L : finiteAbelianExtensions K Ω, (fiberOver c L).Nonempty := fun L ↦ by
    have := L.2.1
    have := L.2.2
    exact restrictAb_surjective (L : IntermediateField K Ω) _ _
  have hdir : Directed (· ⊇ ·) (fiberOver (Ω := Ω) c) := by
    intro L₁ L₂
    have := L₁.2.1
    have := L₁.2.2
    have := L₂.2.1
    have := L₂.2.2
    refine ⟨⟨(L₁ : IntermediateField K Ω) ⊔ L₂, inferInstance, inferInstance⟩, fun τ hτ ↦ ?_,
      fun τ hτ ↦ ?_⟩
    · exact restrictAb_eq_reciprocityMap_of_le le_sup_left hτ
    · exact restrictAb_eq_reciprocityMap_of_le le_sup_right hτ
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fiberOver c) hdir hne (fun L ↦ (hcl L).isCompact) hcl
  refine ⟨τ, fun L _ _ ↦ ?_⟩
  exact Set.mem_iInter.1 hτ ⟨L, inferInstance, inferInstance⟩

def artinMap : IdeleClassGroup K →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) where
  toFun c := (exists_restrictAb_eq_reciprocityMap K Ω c).choose
  map_one' := ext_restrictAb fun L _ _ ↦ by
    rw [(exists_restrictAb_eq_reciprocityMap K Ω 1).choose_spec L, map_one, map_one]
  map_mul' c d := ext_restrictAb fun L _ _ ↦ by
    rw [(exists_restrictAb_eq_reciprocityMap K Ω (c * d)).choose_spec L, map_mul, map_mul,
      (exists_restrictAb_eq_reciprocityMap K Ω c).choose_spec L,
      (exists_restrictAb_eq_reciprocityMap K Ω d).choose_spec L]

variable {K Ω}

@[simp]
theorem restrictAb_artinMap (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
    (c : IdeleClassGroup K) :
    restrictAb L (le_maximalAbelianExtension L) (artinMap K Ω c) = reciprocityMap K L c :=
  (exists_restrictAb_eq_reciprocityMap K Ω c).choose_spec L

theorem artinMap_apply (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
    (c : IdeleClassGroup K) (l : L) :
    ((artinMap K Ω c ⟨l, le_maximalAbelianExtension L l.2⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((reciprocityMap K L c l : L) : Ω) := by
  rw [← restrictAb_artinMap L c, restrictAb_apply]

theorem continuous_artinMap : Continuous (artinMap K Ω) :=
  continuous_iff_restrictAb.2 fun L _ _ ↦ by
    simp only [restrictAb_artinMap]
    exact continuous_reciprocityMap

end ArtinMap

section Local

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

theorem restrictAb_artinMap_finiteEmbedding (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    restrictAb L (le_maximalAbelianExtension L)
        (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v a))) = localSymbol L v a := by
  rw [restrictAb_artinMap, reciprocityMap_mk, ideleSymbol_finiteEmbedding]

theorem artinMap_finiteEmbedding_apply (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v)
    {Ωv : Type*} [Field Ωv] [Algebra (v.adicCompletion K) Ωv] [IsSepClosure (v.adicCompletion K) Ωv]
    (ι : w.1.adicCompletion L →ₐ[v.adicCompletion K] Ωv) (a : (v.adicCompletion K)ˣ) (l : L) :
    ι (algebraMap L (w.1.adicCompletion L)
        (restrictAb L (le_maximalAbelianExtension L)
          (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v a))) l)) =
      ((localArtinMap (v.adicCompletion K) Ωv a
        ⟨ι (algebraMap L (w.1.adicCompletion L) l), apply_mem_maximalAbelianExtension ι _⟩ :
          maximalAbelianExtension (v.adicCompletion K) Ωv) : Ωv) := by
  rw [restrictAb_artinMap_finiteEmbedding, algebraMap_localSymbol_apply,
    normResidueSymbol_apply_eq_localArtinMap]

end Local

end

end GroundTheory.Global
