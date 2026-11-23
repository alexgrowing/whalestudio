import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

universe u

noncomputable section

section Restrict

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) [Normal F L]

def gsRestrictGal : galUnramifiedOutside F Ω S →* (L ≃ₐ[F] L) :=
  letI : Algebra L (maxUnramifiedOutside F Ω S) := (gsEmbedding hL).toRingHom.toAlgebra
  haveI : IsScalarTower F L (maxUnramifiedOutside F Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((gsEmbedding hL).commutes a).symm
  AlgEquiv.restrictNormalHom L

theorem gsEmbedding_gsRestrictGal (σ : galUnramifiedOutside F Ω S) (l : L) :
    gsEmbedding hL (gsRestrictGal hL σ l) = σ (gsEmbedding hL l) := by
  let _ : Algebra L (maxUnramifiedOutside F Ω S) := (gsEmbedding hL).toRingHom.toAlgebra
  have : IsScalarTower F L (maxUnramifiedOutside F Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((gsEmbedding hL).commutes a).symm
  exact AlgEquiv.restrictNormal_commutes σ L l

theorem gsRestrictGal_eq_iff (σ : galUnramifiedOutside F Ω S) (τ : L ≃ₐ[F] L) :
    gsRestrictGal hL σ = τ ↔ ∀ l : L, σ (gsEmbedding hL l) = gsEmbedding hL (τ l) := by
  constructor
  · rintro rfl l
    exact (gsEmbedding_gsRestrictGal hL σ l).symm
  · intro h
    ext l
    exact (gsEmbedding hL).injective ((gsEmbedding_gsRestrictGal hL σ l).trans (h l))

theorem gsRestrictGal_eq_one_iff (σ : galUnramifiedOutside F Ω S) :
    gsRestrictGal hL σ = 1 ↔ σ ∈ gsOpenSubgroup S hL := by
  rw [gsRestrictGal_eq_iff, mem_gsOpenSubgroup_iff]
  rfl

theorem ker_gsRestrictGal :
    (gsRestrictGal hL).ker = (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) :=
  Subgroup.ext fun σ => (MonoidHom.mem_ker).trans (gsRestrictGal_eq_one_iff hL σ)

theorem gsOpenSubgroup_normal :
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal := by
  rw [← ker_gsRestrictGal hL]
  exact MonoidHom.normal_ker _

theorem gsRestrictGal_surjective : Function.Surjective (gsRestrictGal hL) := by
  let _ : Algebra L (maxUnramifiedOutside F Ω S) := (gsEmbedding hL).toRingHom.toAlgebra
  have : IsScalarTower F L (maxUnramifiedOutside F Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((gsEmbedding hL).commutes a).symm
  exact AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (maxUnramifiedOutside F Ω S)

def gsQuotientGalEquiv [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal] :
    galUnramifiedOutside F Ω S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) ≃*
      (L ≃ₐ[F] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_gsRestrictGal hL).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (gsRestrictGal_surjective hL))

@[simp]
theorem gsQuotientGalEquiv_mk
    [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal]
    (σ : galUnramifiedOutside F Ω S) :
    gsQuotientGalEquiv hL (QuotientGroup.mk σ) = gsRestrictGal hL σ :=
  rfl

variable (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

def gsDecompGroup (v : S) : Subgroup (L ≃ₐ[F] L) :=
  ((gsRestrictGal hL).comp (gsFinFamily S ιs v).toMonoidHom).range

theorem mem_gsDecompGroup_iff (v : S) (τ : L ≃ₐ[F] L) :
    τ ∈ gsDecompGroup hL ιs v ↔ ∃ g, gsRestrictGal hL (gsFinFamily S ιs v g) = τ :=
  Iff.rfl

theorem map_range_gsQuotientGalEquiv
    [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal] (v : S) :
    ((QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))).comp
        (gsFinFamily S ιs v).toMonoidHom).range.map (gsQuotientGalEquiv hL).toMonoidHom =
      gsDecompGroup hL ιs v := by
  rw [MonoidHom.map_range]
  rfl

end Restrict

section Real

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  {L : FiniteSubfield} [Fact (K ≤ L)] [Normal K.1 L.1]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

def gsRealDecompGroup (v : {v : InfinitePlace K.1 // v.IsReal}) : Subgroup (L.1 ≃ₐ[K.1] L.1) :=
  ((gsRestrictGal hL).comp (gsRealFamily S ιr v).toMonoidHom).range

theorem mem_gsRealDecompGroup_iff (v : {v : InfinitePlace K.1 // v.IsReal}) (τ : L.1 ≃ₐ[K.1] L.1) :
    τ ∈ gsRealDecompGroup S ιr hL v ↔ ∃ g, gsRestrictGal hL (gsRealFamily S ιr v g) = τ :=
  Iff.rfl

end Real

end

end GroundTheory.ProfCoh
