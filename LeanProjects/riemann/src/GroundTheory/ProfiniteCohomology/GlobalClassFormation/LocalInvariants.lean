import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfRange
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolReal
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolSep
import GroundTheory.GlobalFields.InfiniteNormIndex.LocalSymbol
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped NumberField.LiesOver DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Infinite

variable (v : InfinitePlace K.1)

theorem exists_infCompletion_algEquiv : ∃ (F : FiniteSubfield) (_ : Fact (K ≤ F)) (w : v.placesOver F.1),
    Nonempty ((w : InfinitePlace F.1).Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion) := by
  obtain ⟨ι⟩ : Nonempty (ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) := nonempty_algHom_of_isSepClosed
  obtain ⟨p, hp⟩ := exists_level_infCompletionEmbedding_surjective ι
  exact ⟨p.1, inferInstance, infPlaceOfEmbedding ι p.1, ⟨AlgEquiv.ofBijective (infCompletionEmbedding ι p.1)
    ⟨(infCompletionEmbedding ι p.1).toRingHom.injective, hp p le_rfl⟩⟩⟩

instance finiteDimensional_infAlgClosure :
    FiniteDimensional v.Completion (AlgebraicClosure v.Completion) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  exact LinearEquiv.finiteDimensional e.toLinearEquiv

instance charZero_infCompletion : CharZero v.Completion :=
  charZero_of_injective_algebraMap (algebraMap K.1 v.Completion).injective

instance isGalois_infAlgClosure : IsGalois v.Completion (AlgebraicClosure v.Completion) :=
  inferInstance

theorem infAlgClosure_finrank_le_two :
    Module.finrank v.Completion (AlgebraicClosure v.Completion) ≤ 2 := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  rw [← e.toLinearEquiv.finrank_eq]
  by_cases h : v.IsReal ∧ (w : InfinitePlace F.1).IsComplex
  · exact ((InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace F.1)).2 h).le
  · rw [(InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace F.1)).2 h]
    norm_num

theorem infAlgClosure_mul_mem_range_norm : ∀ a b : v.Completionˣ,
    (a : v.Completion) ∉ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) →
    (b : v.Completion) ∉ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) →
    ((a * b : v.Completionˣ) : v.Completion) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) := by
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have hrange : Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion) =
      Set.range (Algebra.norm v.Completion : (w : InfinitePlace F.1).Completion → v.Completion) := by
    ext c
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, Algebra.norm_eq_of_algEquiv e.symm y⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, Algebra.norm_eq_of_algEquiv e y⟩
  have hmem : ∀ c : v.Completionˣ, (c : v.Completion) ∈
      Set.range (Algebra.norm v.Completion : (w : InfinitePlace F.1).Completion → v.Completion) ↔
      c ∈ InfinitePlace.normSubgroup v (w : InfinitePlace F.1) := by
    intro c
    constructor
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [Algebra.norm_zero] at hy
        exact c.ne_zero hy.symm
      exact ⟨Units.mk0 y hy0, Units.ext hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, congrArg Units.val hy⟩
  intro a b ha hb
  rw [hrange, hmem] at ha hb ⊢
  by_cases h : v.IsReal ∧ (w : InfinitePlace F.1).IsComplex
  · rw [InfinitePlace.mem_normSubgroup_iff h.1 h.2] at ha hb ⊢
    have ha' : InfinitePlace.Completion.extensionEmbeddingOfIsReal h.1 (a : v.Completion) < 0 :=
      lt_of_le_of_ne (not_lt.1 ha) ((map_ne_zero _).2 a.ne_zero)
    have hb' : InfinitePlace.Completion.extensionEmbeddingOfIsReal h.1 (b : v.Completion) < 0 :=
      lt_of_le_of_ne (not_lt.1 hb) ((map_ne_zero _).2 b.ne_zero)
    rw [Units.val_mul, map_mul]
    exact mul_pos_of_neg_of_neg ha' hb'
  · exact absurd (InfinitePlace.normSubgroup_eq_top (w : InfinitePlace F.1) h ▸ Subgroup.mem_top a) ha

end Infinite

def placeInv : ∀ v : Place K.1, localGaloisCohomology K 2 v →+ QZ
  | .inl v => quadraticInv v.Completion (AlgebraicClosure v.Completion) (infAlgClosure_finrank_le_two v)
      (infAlgClosure_mul_mem_range_norm v)
  | .inr v => brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))

theorem placeInv_injective : ∀ v : Place K.1, Function.Injective (placeInv v)
  | .inl v => quadraticInv_injective v.Completion (AlgebraicClosure v.Completion)
      (infAlgClosure_finrank_le_two v) (infAlgClosure_mul_mem_range_norm v)
  | .inr v => (brauerInvZOfIsSepClosure_bijective (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1))).1

theorem placeInv_bijective_inr (v : HeightOneSpectrum (𝓞 K.1)) :
    Function.Bijective (placeInv (K := K) (.inr v)) :=
  brauerInvZOfIsSepClosure_bijective (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))

variable (K) in

def sumPlaceInv : (⨁ v : Place K.1, localGaloisCohomology K 2 v) →+ QZ :=
  by classical exact DirectSum.toAddMonoid fun v => placeInv v

open Classical in

theorem sumPlaceInv_of (v : Place K.1) (t : localGaloisCohomology K 2 v) :
    sumPlaceInv K (DirectSum.of _ v t) = placeInv v t := by
  unfold sumPlaceInv
  convert DirectSum.toAddMonoid_of (fun v => placeInv (K := K) v) v t

end

end GroundTheory.ProfCoh
