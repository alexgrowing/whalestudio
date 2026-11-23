import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.FinitePlaces
import GroundTheory.GlobalFields.GlobalReciprocity.RealPlaces
import GroundTheory.GlobalFields.NormResidueSymbol.Surjective
import GroundTheory.GlobalFields.Adele.IdeleBasis

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup Filter Topology

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

theorem range_ideleNorm_mem_nhds_one :
    ((ideleNorm K L).range : Set (IdeleGroup K)) ∈ 𝓝 1 := by
  classical
  let V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ := fun v ↦
    ((finiteLocalNorm L v).range : Set (v.adicCompletion K)ˣ) ∩
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)
  have hV : ∀ᶠ v in cofinite, V v =
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) := by
    filter_upwards [eventually_map_integerUnitsOver_eq (K := K) L] with v hv
    refine Set.inter_eq_right.2 ?_
    intro u hu
    have hu' : u ∈ (integerUnitsOver L v).map (finiteLocalNorm L v) := by
      rw [hv]
      exact hu
    obtain ⟨y, -, rfl⟩ := hu'
    exact ⟨y, rfl⟩
  have hopen := (IdeleGroup.isTopologicalBasis K).isOpen
    ⟨fun w ↦ ((infiniteLocalNorm L w).range : Set (w.Completion)ˣ), V,
      fun w ↦ isOpen_range_infiniteLocalNorm w,
      fun v ↦ (isOpen_range_finiteLocalNorm v).inter (isOpen_units_adicCompletionIntegers K v),
      hV, rfl⟩
  refine mem_of_superset (hopen.mem_nhds ⟨fun w ↦ ?_, fun v ↦ ⟨?_, ?_⟩⟩) ?_
  · rw [map_one]
    exact one_mem _
  · rw [map_one]
    exact one_mem (finiteLocalNorm L v).range
  · rw [map_one]
    exact one_mem (Submonoid.ofClass (v.adicCompletionIntegers K)).units
  · rintro x ⟨hinf, hfin⟩
    exact mem_range_ideleNorm_of_forall x (fun v ↦ (hfin v).1) hinf

end IdeleNorm

theorem Abelianization.of_injective_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G] :
    Function.Injective (Abelianization.of : G →* Abelianization G) := by
  rw [← MonoidHom.ker_eq_bot_iff, Abelianization.ker_of, commutator_eq_bot]

namespace IdeleClassLimit

open FiniteSubfield

section Main

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

theorem abstractSymbol_mk (x : IdeleGroup K.1) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 x) = Abelianization.of (ideleSymbol K.1 L.1 x) := by
  set f : IdeleGroup K.1 →* Abelianization (L.1 ≃ₐ[K.1] L.1) :=
    (abstractSymbol K L).comp (IdeleClassGroup.mk K.1) with hf
  set g : IdeleGroup K.1 →* Abelianization (L.1 ≃ₐ[K.1] L.1) :=
    Abelianization.of.comp (ideleSymbol K.1 L.1) with hg
  have hle : localEmbeddingSubgroup K.1 ≤ f.eqLocus g :=
    sup_le (iSup_le fun v ↦ by
        rintro _ ⟨a, rfl⟩
        change abstractSymbol K L (IdeleClassGroup.mk K.1 (finiteEmbedding v a)) =
          Abelianization.of (ideleSymbol K.1 L.1 (finiteEmbedding v a))
        rw [abstractSymbol_mk_finiteEmbedding, ideleSymbol_finiteEmbedding])
      (iSup_le fun w ↦ by
        rintro _ ⟨a, rfl⟩
        change abstractSymbol K L (IdeleClassGroup.mk K.1 (infiniteEmbedding w a)) =
          Abelianization.of (ideleSymbol K.1 L.1 (infiniteEmbedding w a))
        rw [abstractSymbol_mk_infiniteEmbedding, ideleSymbol_infiniteEmbedding])
  have hfN : ∀ y : IdeleGroup L.1, f (ideleNorm K.1 L.1 y) = 1 := fun y ↦
    abstractSymbol_ideleClassNorm_eq_one K L (IdeleClassGroup.mk L.1 y)
  have hgN : ∀ y : IdeleGroup L.1, g (ideleNorm K.1 L.1 y) = 1 := fun y ↦ by
    change Abelianization.of (ideleSymbol K.1 L.1 (ideleNorm K.1 L.1 y)) = 1
    rw [ideleSymbol_ideleNorm, map_one]
  obtain ⟨h, hh, ⟨y, hy⟩⟩ :=
    exists_mem_localEmbeddingSubgroup_inv_mul_mem (IdeleNorm.range_ideleNorm_mem_nhds_one L.1) x
  have hx : x = h * ideleNorm K.1 L.1 y := by rw [hy, mul_inv_cancel_left]
  change f x = g x
  rw [hx, map_mul, map_mul, hfN, hgN, (hle hh : f h = g h)]

theorem abstractSymbol_comp_mk :
    (abstractSymbol K L).comp (IdeleClassGroup.mk K.1) =
      Abelianization.of.comp (ideleSymbol K.1 L.1) :=
  MonoidHom.ext (abstractSymbol_mk K L)

theorem ideleSymbol_diagonal (a : K.1ˣ) : ideleSymbol K.1 L.1 (diagonal K.1 a) = 1 := by
  apply Abelianization.of_injective_of_isMulCommutative
  rw [← abstractSymbol_mk, IdeleClassGroup.mk_diagonal, map_one, map_one]

theorem range_diagonal_le_ker_ideleSymbol :
    (diagonal K.1).range ≤ (ideleSymbol K.1 L.1).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleSymbol_diagonal K L a

abbrev classSymbol : IdeleClassGroup K.1 →* (L.1 ≃ₐ[K.1] L.1) :=
  CyclotomicSymbol.ideleClassSymbol L.1 (range_diagonal_le_ker_ideleSymbol K L)

theorem classSymbol_mk (x : IdeleGroup K.1) :
    classSymbol K L (IdeleClassGroup.mk K.1 x) = ideleSymbol K.1 L.1 x :=
  rfl

theorem abstractSymbol_eq_classSymbol :
    abstractSymbol K L = Abelianization.of.comp (classSymbol K L) := by
  refine MonoidHom.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K.1 c
  exact abstractSymbol_mk K L x

theorem continuous_classSymbol : Continuous (classSymbol K L) :=
  CyclotomicSymbol.continuous_ideleClassSymbol _

theorem classSymbol_surjective : Function.Surjective (classSymbol K L) :=
  CyclotomicSymbol.ideleClassSymbol_surjective _

theorem ker_abstractSymbol :
    (abstractSymbol K L).ker = (FiniteSubfield.ideleClassNorm hKL.out).range := by
  ext c
  rw [MonoidHom.mem_ker, abstractSymbol_apply]
  have hinj : Function.Injective (Abelianization.map (quotientGaloisEquiv K L).toMonoidHom) :=
    fun a b hab ↦ (quotientGaloisEquiv K L).abelianizationCongr.injective hab
  rw [← map_one (Abelianization.map (quotientGaloisEquiv K L).toMonoidHom), hinj.eq_iff,
    ← map_one (reciprocityEquiv K L).symm, (reciprocityEquiv K L).symm.injective.eq_iff]
  constructor
  · intro h
    change (QuotientGroup.mk (fixedEquiv K c) : GroundTheory.LocalField.Abstract.tateZero IdeleClassLimit
      (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) L.openSubgroup) = 1 at h
    rw [QuotientGroup.eq_one_iff] at h
    obtain ⟨b, hb⟩ := h
    obtain ⟨d, rfl⟩ := (fixedEquiv L).surjective b
    refine ⟨d, (fixedEquiv K).injective ?_⟩
    rw [← norm_fixedEquiv hKL.out d]
    exact hb
  · rintro ⟨d, rfl⟩
    exact normClass_ideleClassNorm K L d

theorem ker_classSymbol :
    (classSymbol K L).ker = (FiniteSubfield.ideleClassNorm hKL.out).range := by
  ext c
  rw [← ker_abstractSymbol K L, MonoidHom.mem_ker, MonoidHom.mem_ker, abstractSymbol_eq_classSymbol K L,
    MonoidHom.comp_apply, ← map_one Abelianization.of,
    Abelianization.of_injective_of_isMulCommutative.eq_iff]

def classSymbolEquiv :
    IdeleClassGroup K.1 ⧸ (FiniteSubfield.ideleClassNorm hKL.out).range ≃* (L.1 ≃ₐ[K.1] L.1) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_classSymbol K L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (classSymbol_surjective K L))

theorem classSymbolEquiv_mk (x : IdeleGroup K.1) :
    classSymbolEquiv K L (QuotientGroup.mk (IdeleClassGroup.mk K.1 x)) = ideleSymbol K.1 L.1 x :=
  rfl

theorem ker_ideleSymbol :
    (ideleSymbol K.1 L.1).ker = (diagonal K.1).range ⊔ (ideleNorm K.1 L.1).range := by
  refine le_antisymm (fun x hx ↦ ?_)
    (sup_le (range_diagonal_le_ker_ideleSymbol K L) (range_ideleNorm_le_ker_ideleSymbol L.1))
  have hc : IdeleClassGroup.mk K.1 x ∈ (classSymbol K L).ker := hx
  rw [ker_classSymbol] at hc
  obtain ⟨c, hc⟩ := hc
  obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L.1 c
  have hy : IdeleClassGroup.mk K.1 (ideleNorm K.1 L.1 y) = IdeleClassGroup.mk K.1 x := hc
  have hd : (ideleNorm K.1 L.1 y)⁻¹ * x ∈ (diagonal K.1).range := by
    rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have hx : x = ideleNorm K.1 L.1 y * ((ideleNorm K.1 L.1 y)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨y, rfl⟩) (Subgroup.mem_sup_left hd)

end Main

end IdeleClassLimit

end

end GroundTheory.Global
