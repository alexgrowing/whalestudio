import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero AdeleBaseChange
open scoped NumberField.AdeleRing

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace AdeleBaseChange

theorem continuous_finiteCompletionMap {M M' : Type*} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) :
    Continuous (finiteCompletionMap τ w') :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  SemiLocal.continuous_completionMap (below M w') w'

omit [NumberField K] in

theorem valued_finiteCompletionMap (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L))
    (y : (comapPrime (σ : L ≃+* L) w).adicCompletion L) :
    Valued.v (finiteCompletionMap (σ : L ≃+* L) w y) = Valued.v y := by
  have hL : ∀ l : L, Valued.v (finiteCompletionMap (σ : L ≃+* L) w
      (algebraMap L ((comapPrime (σ : L ≃+* L) w).adicCompletion L) l)) =
        Valued.v (algebraMap L ((comapPrime (σ : L ≃+* L) w).adicCompletion L) l) := by
    intro l
    rw [finiteCompletionMap_algebraMap]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, valuedAdicCompletion_eq_valuation']
    rw [comapPrime_eq_inv_smul]
    conv_lhs => rw [← smul_inv_smul σ w]
    exact SemiLocal.valuation_smul σ (σ⁻¹ • w) l
  have hclosed : IsClosed {y : (comapPrime (σ : L ≃+* L) w).adicCompletion L |
      Valued.v (finiteCompletionMap (σ : L ≃+* L) w y) = Valued.v y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y0 hy0
    have h0 : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    have h1 : Valued.v y0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (finiteCompletionMap (σ : L ≃+* L) w y0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2
        ((map_ne_zero_iff _ (finiteCompletionMap (σ : L ≃+* L) w).injective).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_finiteCompletionMap _ w).continuousAt.preimage_mem_nhds
        (Valued.locally_const h2)] with y hy hy'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hy hy' hy0 ⊢
    rwa [hy, hy']
  exact (HeightOneSpectrum.denseRange_algebraMap L (comapPrime (σ : L ≃+* L) w)).induction_on
    (p := fun y ↦ Valued.v (finiteCompletionMap (σ : L ≃+* L) w y) = Valued.v y) y hclosed hL

omit [NumberField K] [NumberField L] in

theorem below_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    below K (σ • w) = below K w :=
  HeightOneSpectrum.ext (Ideal.under_smul (𝓞 K) w.asIdeal σ)

end AdeleBaseChange

namespace IdeleGroup

omit [NumberField K] in

theorem ord_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) (w : HeightOneSpectrum (𝓞 L)) :
    ord w (σ • x) = ord (σ⁻¹ • w) x := by
  simp only [ord]
  rw [coe_smul_idele, smul_snd, valued_finiteCompletionMap, comapPrime_eq_inv_smul]

variable (L) in

def placesAbove (S : Set (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 L)) :=
  below K ⁻¹' S

omit [NumberField K] [NumberField L] in
theorem mem_placesAbove {S : Set (HeightOneSpectrum (𝓞 K))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesAbove L S ↔ below K w ∈ S :=
  Iff.rfl

omit [NumberField K] [NumberField L] in
theorem placesAbove_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    placesAbove L S ⊆ placesAbove L T :=
  fun _ hw ↦ h hw

theorem placesAbove_finite {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    (placesAbove L S).Finite :=
  hS.preimage' fun v _ ↦
    (Set.finite_range (Subtype.val : SemiLocal.PlacesOver L v → HeightOneSpectrum (𝓞 L))).subset
      fun w hw ↦ ⟨⟨w, (below_eq_iff w v).1 hw⟩, rfl⟩

omit [NumberField K] [NumberField L] in

theorem smul_mem_placesAbove_iff (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (w : HeightOneSpectrum (𝓞 L)) : σ • w ∈ placesAbove L S ↔ w ∈ placesAbove L S := by
  rw [mem_placesAbove, mem_placesAbove, below_smul]

variable (S : Set (HeightOneSpectrum (𝓞 K)))

omit [NumberField K] in

theorem smul_mem_sIdeles_placesAbove (σ : L ≃ₐ[K] L) {x : IdeleGroup L}
    (hx : x ∈ sIdeles (placesAbove L S)) : σ • x ∈ sIdeles (placesAbove L S) := fun w hw ↦ by
  rw [ord_smul]
  exact hx _ fun h ↦ hw ((smul_mem_placesAbove_iff S σ⁻¹ w).1 h)

instance : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles (placesAbove L S)) where
  smul σ x := ⟨σ • (x : IdeleGroup L), smul_mem_sIdeles_placesAbove S σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : IdeleGroup L))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : IdeleGroup L))
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : IdeleGroup L) y)
  smul_one σ := Subtype.ext (smul_one σ)

omit [NumberField K] in
@[simp]
theorem coe_smul_sIdeles (σ : L ≃ₐ[K] L) (x : sIdeles (placesAbove L S)) :
    ((σ • x : sIdeles (placesAbove L S)) : IdeleGroup L) = σ • (x : IdeleGroup L) :=
  rfl

omit [NumberField K] in

theorem sIdelesToIdeleClassGroup_smul (σ : L ≃ₐ[K] L) (x : sIdeles (placesAbove L S)) :
    sIdelesToIdeleClassGroup (placesAbove L S) (σ • x) =
      σ • sIdelesToIdeleClassGroup (placesAbove L S) x := by
  rw [sIdelesToIdeleClassGroup_apply, sIdelesToIdeleClassGroup_apply, smul_mk, coe_smul_sIdeles]

omit [NumberField K] in

theorem exists_finset_superset_sup_sIdeles_placesAbove_eq_top
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      (diagonal L).range ⊔ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_sup_sIdeles_eq_top (K := L)
  refine ⟨S₀ ∪ T.image (below K), Finset.subset_union_left,
    sup_sIdeles_eq_top_of_subset (fun w hw ↦ ?_) hT⟩
  exact Finset.mem_coe.2
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hw)))

omit [NumberField K] in

theorem sUnits_sIdeles_placesAbove_exact
    (h : (diagonal L).range ⊔ sIdeles (placesAbove L S) = ⊤) :
    Function.Injective (sUnitsToSIdeles (placesAbove L S)) ∧
      (sUnitsToSIdeles (placesAbove L S)).range =
        (sIdelesToIdeleClassGroup (placesAbove L S)).ker ∧
      Function.Surjective (sIdelesToIdeleClassGroup (placesAbove L S)) :=
  sUnits_sIdeles_exact _ h

end IdeleGroup

end

end GroundTheory.Global
