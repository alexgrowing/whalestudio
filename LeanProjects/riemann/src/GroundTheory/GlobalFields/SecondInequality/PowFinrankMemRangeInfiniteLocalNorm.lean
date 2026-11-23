import Mathlib
import GroundTheory.GlobalFields.SecondInequality.Statement
import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import GroundTheory.GlobalFields.ExistenceTheorem.LocalPowers

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Module IntermediateField
open GroundTheory.ProfCoh IdeleGroup IdeleNorm SemiLocal
open scoped TensorProduct NumberField.LiesOver

section Splitting

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem algHom_mem_fieldRange_of_pow_eq {L F E : Type*} [Field L] [Field F] [Field E]
    [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    {a : K} {α : L} (hα : α ^ n = algebraMap K L a) (hgen : K⟮α⟯ = ⊤) (ι : L →ₐ[K] E)
    {x : F} (hx : x ^ n = algebraMap K F a) (m : L) :
    ι m ∈ (algebraMap F E).fieldRange := by
  have hαr : ι α ∈ (algebraMap F E).fieldRange := by
    by_cases hx0 : x = 0
    · have ha : a = 0 := by
        rw [hx0, zero_pow (NeZero.ne n)] at hx
        exact (algebraMap K F).injective (by rw [← hx, map_zero])
      rw [ha, map_zero, pow_eq_zero_iff (NeZero.ne n)] at hα
      rw [hα, map_zero]
      exact zero_mem _
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hζ' : IsPrimitiveRoot (algebraMap K E ζ) n :=
      hζ.map_of_injective (algebraMap K E).injective
    have hx0' : algebraMap F E x ≠ 0 := (map_ne_zero _).2 hx0
    have hpow : ι α ^ n = algebraMap F E x ^ n := by
      rw [← map_pow, hα, ι.commutes, ← map_pow, hx, ← IsScalarTower.algebraMap_apply]
    have hroot : (ι α / algebraMap F E x) ^ n = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero _ hx0')]
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine ⟨algebraMap K F ζ ^ k * x, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hk, div_mul_cancel₀ _ hx0']
  let J : IntermediateField K E := Subfield.toIntermediateField (algebraMap F E).fieldRange
    fun c ↦ ⟨algebraMap K F c, (IsScalarTower.algebraMap_apply K F E c).symm⟩
  have hle : K⟮α⟯ ≤ J.comap ι := adjoin_simple_le_iff.2 hαr
  rw [hgen] at hle
  exact hle (Set.mem_univ m)

variable [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem splitsCompletely_of_pow_eq {a : K} {α : L} (hα : α ^ n = algebraMap K L a)
    (hgen : K⟮α⟯ = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (h : ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) a) :
    SplitsCompletely L v := by
  obtain ⟨x, hx⟩ := h
  rw [splitsCompletely_iff_forall_finrank]
  intro w
  let g := (Pi.evalAlgHom (v.adicCompletion K) _ w).comp (tensorEquiv L v).toAlgHom
  exact finrank_eq_one_of_tensor_surjective g
    ((Function.surjective_eval w).comp (tensorEquiv L v).surjective)
    fun m ↦ algHom_mem_fieldRange_of_pow_eq hα hgen
      ((g.restrictScalars K).comp Algebra.TensorProduct.includeRight) hx m

end Splitting

section LocalNorms

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem pow_finrank_mem_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletion K)ˣ) : y ^ finrank K L ∈ (finiteLocalNorm L v).range := by
  refine ⟨fun w ↦ Units.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) :
    v.adicCompletion K →* w.1.adicCompletion L) y, ?_⟩
  apply Units.ext
  rw [coe_finiteLocalNorm, Units.val_pow_eq_pow_val, ← sum_finrank_eq L v,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.coe_map]
  exact Algebra.norm_algebraMap (S := w.1.adicCompletion L) (y : v.adicCompletion K)

theorem pow_finrank_mem_range_infiniteLocalNorm (v : InfinitePlace K) (y : (v.Completion)ˣ) :
    y ^ finrank K L ∈ (infiniteLocalNorm L v).range := by
  classical
  refine ⟨fun w ↦ Units.map (algebraMap v.Completion (w : InfinitePlace L).Completion :
    v.Completion →* (w : InfinitePlace L).Completion) y, ?_⟩
  apply Units.ext
  rw [coe_infiniteLocalNorm, Units.val_pow_eq_pow_val,
    ← GroundTheory.Global.InfinitePlace.sum_finrank_completion (L := L) v, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.coe_map]
  exact Algebra.norm_algebraMap (S := (w : InfinitePlace L).Completion) (y : v.Completion)

end LocalNorms

section Main

universe u

theorem not_mem_bot_of_adjoin_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hgen : K⟮α⟯ = ⊤) (h1 : finrank K L ≠ 1) : α ∉ (⊥ : IntermediateField K L) := by
  intro hα
  have hbot : (⊤ : IntermediateField K L) = ⊥ := by
    rw [← hgen]
    exact adjoin_simple_eq_bot_iff.2 hα
  have := IntermediateField.finrank_eq_one_iff.2 hbot
  rw [IntermediateField.finrank_top'] at this
  exact h1 this

theorem FirstInequality.secondInequalityRoots (hFI : FirstInequality.{u}) :
    SecondInequalityRoots.{u} := by
  intro K L _ _ _ _ _ _ _ p hp hroots hdeg
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  have hK : (primitiveRoots (finrank K L) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots finrank_pos).2 (hdeg ▸ hζ)⟩
  obtain ⟨α, ⟨a₀, ha₀⟩, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  rw [hdeg] at ha₀
  have h1 : finrank K L ≠ 1 := by rw [hdeg]; exact hp.ne_one
  have hαK := not_mem_bot_of_adjoin_eq_top hgen h1
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, pow_eq_zero_iff hp.ne_zero] at ha₀
    exact hαK (ha₀ ▸ zero_mem _)
  set a : Kˣ := Units.mk0 a₀ ha₀0 with ha_def
  have hα : α ^ p = algebraMap K L (a : K) := by rw [Units.val_mk0, ha₀]

  have hap : a ∉ unitsPow K p := by
    intro h
    obtain ⟨b, hb⟩ := mem_unitsPow.1 h
    have hb0 : algebraMap K L (b : K) ≠ 0 := (map_ne_zero _).2 b.ne_zero
    have hroot : (α / algebraMap K L (b : K)) ^ p = 1 := by
      rw [div_pow, hα, ← map_pow, ← Units.val_pow_eq_pow_val, hb,
        div_self ((map_ne_zero _).2 a.ne_zero)]
    have hζ' : IsPrimitiveRoot (algebraMap K L ζ) p :=
      hζ.map_of_injective (algebraMap K L).injective
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine hαK ⟨ζ ^ k * b, ?_⟩
    show algebraMap K L (ζ ^ k * (b : K)) = α
    rw [map_mul, map_pow, hk, div_mul_cancel₀ _ hb0]

  obtain ⟨S₀, hS₀⟩ := exists_finset_sup_sIdeles_eq_top (K := K)
  have hfp : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 K)}) ?_).subset fun v hv ↦ ?_
    · rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    · exact Ideal.dvd_span_singleton.2 hv
  have hfa : {v : HeightOneSpectrum (𝓞 K) | ord v (diagonal K a) ≠ 0}.Finite :=
    eventually_ord_eq_zero (diagonal K a)
  set S : Finset (HeightOneSpectrum (𝓞 K)) := S₀ ∪ hfp.toFinset ∪ hfa.toFinset with hS
  have hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv ↦ by
    simp [S, hv]
  have hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ :=
    sup_sIdeles_eq_top_of_subset (fun v hv ↦ by simp [S, Finset.mem_coe.1 hv]) hS₀
  have haS : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
    refine (diagonal_mem_sIdeles_iff _ a).1 fun v hv ↦ ?_
    by_contra h
    exact hv (by simp [S, h])

  obtain ⟨T, hST, -, haT, hidx⟩ := hFI.exists_places_index_map_powerSubgroup S hpS hJ haS hap

  have hnorm : powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))) ≤
      (ideleNorm K L).range := by
    intro x hx
    have hxST := powerSubgroup_le_sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))
      (T : Set (HeightOneSpectrum (𝓞 K))) p hx
    obtain ⟨hxS, hxinf, -⟩ := (mem_localSubgroup _ _ _ _).1 hx
    refine mem_range_ideleNorm_of_forall x (fun v ↦ ?_) (fun w ↦ ?_)
    · by_cases hvS : v ∈ S
      · obtain ⟨y, hy⟩ := hxS v hvS
        rw [← hy, powMonoidHom_apply, ← hdeg]
        exact pow_finrank_mem_range_finiteLocalNorm v y
      by_cases hvT : v ∈ T
      · rw [range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
          (splitsCompletely_of_pow_eq hα hgen v (mem_unitsPowIn.1 (haT v hvT))))]
        exact Subgroup.mem_top _
      · obtain ⟨w⟩ := nonempty_placesOver L v
        have he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1 :=
          Kummer.ramificationIdx_eq_one_of_pow_eq a hα hgen v (fun h ↦ hvS (hpS v h))
            (by rw [haS v hvS, WithZero.log_one]; exact dvd_zero _) w.1.asIdeal
        have hu : finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
          have h := (mem_sIdeles_iff _).1 hxST v (by simp [hvS, hvT])
          rw [Submonoid.mem_units_iff, ← map_inv, coe_finiteProj, coe_finiteProj]
          exact ⟨h.1, h.2⟩
        rw [← map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w he] at hu
        obtain ⟨z, -, hz⟩ := hu
        exact ⟨z, hz⟩
    · obtain ⟨y, hy⟩ := hxinf w
      rw [← hy, powMonoidHom_apply, ← hdeg]
      exact pow_finrank_mem_range_infiniteLocalNorm w y

  have hle : (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K)))
      (T : Set (HeightOneSpectrum (𝓞 K)))).map (IdeleClassGroup.mk K) ≤
        (ideleClassNorm K L).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hnorm hx
    exact ⟨IdeleClassGroup.mk L y, by rw [ideleClassNorm_mk, hy]⟩
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  refine (enatCard_quotient_le_iff _ p).2 ⟨fun h ↦ ?_, Nat.le_of_dvd hp.pos hdvd⟩
  rw [h] at hdvd
  exact hp.ne_zero (Nat.eq_zero_of_zero_dvd hdvd)

end Main

end GroundTheory.Global
