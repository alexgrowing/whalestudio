import Mathlib
import GroundTheory.GlobalFields.InfiniteNormIndex.LocalSymbol
import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
import GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
  NumberField.ComplexEmbedding
open scoped NumberField.LiesOver ComplexConjugate

noncomputable section

section Conj

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isConj_iff_forall {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} :
    IsConj φ σ ↔ ∀ x, φ (σ x) = star (φ x) :=
  ⟨fun h ↦ h.eq, fun h ↦ RingHom.ext fun x ↦ by
    rw [RingHom.comp_apply, conjugate_coe_eq, starRingEnd_apply]
    exact (h x).symm⟩

theorem isConj_conjugate_iff {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} :
    IsConj (conjugate φ) σ ↔ IsConj φ σ := by
  simp only [isConj_iff_forall, conjugate_coe_eq, starRingEnd_apply]
  constructor
  · intro h x
    simpa using congrArg star (h x)
  · intro h x
    rw [h x]

theorem isConj_iff_of_mk_eq {φ ψ : L →+* ℂ} (h : mk φ = mk ψ) (σ : L ≃ₐ[K] L) :
    IsConj φ σ ↔ IsConj ψ σ := by
  rcases mk_eq_iff.1 h with rfl | rfl
  · rfl
  · exact isConj_conjugate_iff.symm

theorem isConj_comp_iff [IsMulCommutative (L ≃ₐ[K] L)] {φ : L →+* ℂ} {σ ν : L ≃ₐ[K] L} :
    IsConj (φ.comp (ν : L →+* L)) σ ↔ IsConj φ σ := by
  have hc : ∀ y, ν (σ y) = σ (ν y) := fun y ↦ by
    rw [← AlgEquiv.mul_apply, mul_comm' ν σ, AlgEquiv.mul_apply]
  have hν : ∀ y, (ν : L →+* L) y = ν y := fun _ ↦ rfl
  simp only [isConj_iff_forall, RingHom.comp_apply, hν]
  constructor
  · intro h y
    have := h (ν.symm y)
    rwa [hc, AlgEquiv.apply_symm_apply] at this
  · intro h y
    rw [hc]
    exact h (ν y)

open scoped Classical in

def conjOfEmbedding (φ : L →+* ℂ) : L ≃ₐ[K] L :=
  if h : ∃ σ : L ≃ₐ[K] L, IsConj φ σ then h.choose else 1

theorem conjOfEmbedding_eq {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} (hσ : IsConj φ σ) :
    conjOfEmbedding φ = σ := by
  have h : ∃ σ : L ≃ₐ[K] L, IsConj φ σ := ⟨σ, hσ⟩
  rw [conjOfEmbedding, dif_pos h]
  exact h.choose_spec.ext hσ

theorem conjOfEmbedding_of_not {φ : L →+* ℂ} (h : ¬ ∃ σ : L ≃ₐ[K] L, IsConj φ σ) :
    conjOfEmbedding (K := K) φ = 1 := by
  rw [conjOfEmbedding, dif_neg h]

theorem conjOfEmbedding_congr {φ ψ : L →+* ℂ}
    (h : ∀ σ : L ≃ₐ[K] L, IsConj φ σ ↔ IsConj ψ σ) :
    conjOfEmbedding (K := K) φ = conjOfEmbedding ψ := by
  by_cases hφ : ∃ σ : L ≃ₐ[K] L, IsConj φ σ
  · obtain ⟨σ, hσ⟩ := hφ
    rw [conjOfEmbedding_eq hσ, conjOfEmbedding_eq ((h σ).1 hσ)]
  · rw [conjOfEmbedding_of_not hφ,
      conjOfEmbedding_of_not fun ⟨σ, hσ⟩ ↦ hφ ⟨σ, (h σ).2 hσ⟩]

theorem conjOfEmbedding_mul_self (φ : L →+* ℂ) :
    conjOfEmbedding (K := K) φ * conjOfEmbedding φ = 1 := by
  by_cases hφ : ∃ σ : L ≃ₐ[K] L, IsConj φ σ
  · obtain ⟨σ, hσ⟩ := hφ
    rw [conjOfEmbedding_eq hσ]
    exact AlgEquiv.ext fun x ↦ isConj_apply_apply hσ x
  · rw [conjOfEmbedding_of_not hφ, mul_one]

variable (K) in

def conjAt (w : InfinitePlace L) : L ≃ₐ[K] L :=
  conjOfEmbedding w.embedding

theorem conjAt_mul_self (w : InfinitePlace L) : conjAt K w * conjAt K w = 1 :=
  conjOfEmbedding_mul_self _

theorem conjAt_of_isReal {w : InfinitePlace L} (hw : w.IsReal) : conjAt K w = 1 :=
  conjOfEmbedding_eq (isConj_one_iff.2 (isReal_iff.1 hw))

theorem isConj_conjAt [IsGalois K L] {w : InfinitePlace L} (hw : w.IsRamified K) :
    IsConj w.embedding (conjAt K w) := by
  obtain ⟨σ, hσ⟩ := exists_isConj_of_isRamified (k := K) (φ := w.embedding) (by rwa [mk_embedding])
  rw [conjAt, conjOfEmbedding_eq hσ]
  exact hσ

theorem conjAt_ne_one [IsGalois K L] {w : InfinitePlace L} (hw : w.IsRamified K) :
    conjAt K w ≠ 1 :=
  (isConj_ne_one_iff (isConj_conjAt hw)).2 fun h ↦
    not_isReal_iff_isComplex.2 (isRamified_iff.1 hw).1 (isReal_iff.2 h)

theorem conjAt_smul [IsMulCommutative (L ≃ₐ[K] L)] (τ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    conjAt K (τ • w) = conjAt K w := by
  refine conjOfEmbedding_congr fun σ ↦ ?_
  have h : mk (τ • w).embedding = mk (w.embedding.comp (τ.symm : L →+* L)) := by
    rw [mk_embedding, ← smul_mk, mk_embedding]
  rw [isConj_iff_of_mk_eq h]
  exact isConj_comp_iff

theorem conjAt_eq [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {v : InfinitePlace K}
    (w w' : v.placesOver L) : conjAt K (w : InfinitePlace L) = conjAt K (w' : InfinitePlace L) := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'
  rw [InfinitePlace.coe_smul_placesOver, conjAt_smul]

end Conj

section Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]

theorem extensionEmbedding_algebraMap_self (l : L) :
    extensionEmbedding w (algebraMap L w.Completion l) = w.embedding l :=
  extensionEmbedding_coe w _

theorem completionConj_algebraMap (hv : v.IsReal) (l : L) :
    InfinitePlace.completionConj (w := w) hv (algebraMap L w.Completion l) =
      algebraMap L w.Completion (conjAt K w l) := by
  by_cases hw : w.IsComplex
  · have hram : w.IsRamified K :=
      isRamified_iff.2 ⟨hw, by rw [InfinitePlace.LiesOver.comap_eq w v]; exact hv⟩
    apply (extensionEmbedding w).injective
    rw [InfinitePlace.extensionEmbedding_completionConj, extensionEmbedding_algebraMap_self,
      extensionEmbedding_algebraMap_self, (isConj_conjAt hram).eq, starRingEnd_apply]
  · have hw' : w.IsReal := not_isComplex_iff_isReal.1 hw
    rw [InfinitePlace.completionConj, dif_neg hw, conjAt_of_isReal hw']
    rfl

end Completion

section Symbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (v : InfinitePlace K)

open scoped Classical in

def infiniteLocalSymbol : v.Completionˣ →* (L ≃ₐ[K] L) :=
  if hv : v.IsReal then
    (InfinitePlace.realSignHom (conjAt K ((IdeleNorm.nonempty_infinitePlacesOver L v).some :
        InfinitePlace L)) (conjAt_mul_self _)).comp
      (Units.map (extensionEmbeddingOfIsReal hv).toMonoidHom)
  else 1

theorem infiniteLocalSymbol_apply (hv : v.IsReal) (w : v.placesOver L) (x : v.Completionˣ) :
    infiniteLocalSymbol L v x =
      if extensionEmbeddingOfIsReal hv x < 0 then conjAt K (w : InfinitePlace L) else 1 := by
  rw [infiniteLocalSymbol, dif_pos hv, MonoidHom.comp_apply, InfinitePlace.realSignHom_apply,
    conjAt_eq _ w]
  rfl

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in

theorem infiniteLocalSymbol_of_not_isReal (hv : ¬ v.IsReal) : infiniteLocalSymbol L v = 1 := by
  rw [infiniteLocalSymbol, dif_neg hv]

theorem algebraMap_infiniteLocalSymbol_apply (w : v.placesOver L) (x : v.Completionˣ) (l : L) :
    algebraMap L (w : InfinitePlace L).Completion (infiniteLocalSymbol L v x l) =
      InfinitePlace.localSymbol v (w : InfinitePlace L) x
        (algebraMap L (w : InfinitePlace L).Completion l) := by
  by_cases hv : v.IsReal
  · rw [infiniteLocalSymbol_apply L v hv w, InfinitePlace.localSymbol_apply v _ hv]
    split_ifs
    · exact (completionConj_algebraMap (w : InfinitePlace L) hv l).symm
    · rfl
  · rw [infiniteLocalSymbol_of_not_isReal L v hv, InfinitePlace.localSymbol_of_not_isReal v _ hv]
    rfl

theorem ker_infiniteLocalSymbol (w : v.placesOver L) :
    (infiniteLocalSymbol L v).ker = InfinitePlace.normSubgroup v (w : InfinitePlace L) := by
  by_cases h2 : v.IsReal ∧ (w : InfinitePlace L).IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hram : (w : InfinitePlace L).IsRamified K :=
      isRamified_iff.2 ⟨hw, by rw [InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v]; exact hv⟩
    ext x
    rw [MonoidHom.mem_ker, infiniteLocalSymbol_apply L v hv w,
      InfinitePlace.mem_normSubgroup_iff hv hw]
    have hx0 : extensionEmbeddingOfIsReal hv x ≠ 0 := (map_ne_zero _).2 x.ne_zero
    constructor
    · intro h
      by_contra hneg
      rw [if_pos (lt_of_le_of_ne (not_lt.1 hneg) hx0)] at h
      exact conjAt_ne_one hram h
    · intro h
      rw [if_neg (not_lt.2 h.le)]
  · rw [InfinitePlace.normSubgroup_eq_top (w : InfinitePlace L) h2, eq_top_iff]
    intro x _
    rw [MonoidHom.mem_ker]
    by_cases hv : v.IsReal
    · have hw : (w : InfinitePlace L).IsReal := not_isComplex_iff_isReal.1 fun hw ↦ h2 ⟨hv, hw⟩
      rw [infiniteLocalSymbol_apply L v hv w, conjAt_of_isReal hw, ite_self]
    · rw [infiniteLocalSymbol_of_not_isReal L v hv, MonoidHom.one_apply]

open scoped Classical in

theorem range_infiniteLocalNorm_le_ker_infiniteLocalSymbol :
    (IdeleNorm.infiniteLocalNorm L v).range ≤ (infiniteLocalSymbol L v).ker := by
  rintro _ ⟨y, rfl⟩
  change ∏ w : v.placesOver L, Units.map (Algebra.norm v.Completion :
    (w : InfinitePlace L).Completion →* v.Completion) (y w) ∈ _
  exact Subgroup.prod_mem _ fun w _ ↦ by
    rw [ker_infiniteLocalSymbol L v w]
    exact ⟨y w, rfl⟩

theorem continuous_infiniteLocalSymbol : Continuous (infiniteLocalSymbol L v) :=
  continuous_monoidHom_of_isOpen_ker _ (Subgroup.isOpen_mono
    (range_infiniteLocalNorm_le_ker_infiniteLocalSymbol L v)
    (IdeleNorm.isOpen_range_infiniteLocalNorm v))

end Symbol

end

end GroundTheory.Global
