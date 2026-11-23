import Mathlib
import GroundTheory.GlobalFields.ExistenceTheorem.PowerIndex
import GroundTheory.GlobalFields.ExistenceTheorem.LocalPowers
import GroundTheory.GlobalFields.IdeleGroups.IndexFormula
import GroundTheory.GlobalFields.IdeleGroups.IndexProductFormula
import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup

noncomputable section

section LocalIndex

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem index_range_powMonoidHom_adicCompletion_mul_norm (v : HeightOneSpectrum (𝓞 K)) :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) *
      ‖(n : v.adicCompletion K)‖ = (n : ℝ) ^ 2 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hζv := hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective
  have hn : ‖(n : v.adicCompletion K)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (natCast_ne_zero_adicCompletion (v := v) (NeZero.ne n))
  rw [index_range_powMonoidHom_adicCompletion v (NeZero.ne n), hζv.card_rootsOfUnity,
    div_mul_cancel₀ _ hn, sq]

omit [NumberField K] in

theorem eq_one_or_eq_two_of_isReal {w : InfinitePlace K} (hw : w.IsReal) : n = 1 ∨ n = 2 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have h := hζ.map_of_injective (InfinitePlace.embedding_of_isReal hw).injective
  set x := InfinitePlace.embedding_of_isReal hw ζ
  have habs : |x| = 1 := by
    have h1 : |x| ^ n = 1 := by rw [← abs_pow, h.pow_eq_one, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg x) (NeZero.ne n)).1 h1
  have hx2 : x ^ 2 = 1 := by rw [← sq_abs, habs, one_pow]
  exact (Nat.dvd_prime Nat.prime_two).1 (h.dvd_of_pow_eq_one 2 hx2)

omit [NumberField K] in

theorem index_range_powMonoidHom_infinitePlaceCompletion_mul_norm (w : InfinitePlace K) :
    ((powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range.index : ℝ) *
      ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ 2 := by
  have hnorm : ‖(n : w.Completion)‖ = n := by
    have h : ‖(n : w.Completion)‖ = w (n : K) := by
      rw [← map_natCast (algebraMap K w.Completion) n]
      exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
    rw [h, InfinitePlace.map_natCast]
  rw [index_range_powMonoidHom_infinitePlaceCompletion w (NeZero.ne n), hnorm]
  rcases w.isReal_or_isComplex with hw | hw
  · rw [hw.mult_eq_one, pow_one]
    rcases eq_one_or_eq_two_of_isReal (n := n) hw with h | h <;> subst h <;> norm_num [hw]
  · have hw' : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
    rw [hw.mult_eq_two]
    simp [hw']

theorem relIndex_powerSubgroup_empty_eq_pow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).relIndex
        (sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))) =
      n ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  have hpf := prod_norm_natCast_mul_prod_infinitePlace (K := K) (NeZero.ne n) S hS
  apply Nat.cast_injective (R := ℝ)
  rw [relIndex_powerSubgroup_empty]
  push_cast
  have key : ((∏ v ∈ S, ((powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index : ℝ)) *
      ∏ w : InfinitePlace K, ((powMonoidHom n : (w.Completion)ˣ →* _).range.index : ℝ)) *
      ((∏ v ∈ S, ‖(n : v.adicCompletion K)‖) *
        ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult) =
      (n : ℝ) ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp_rw [index_range_powMonoidHom_adicCompletion_mul_norm,
      index_range_powMonoidHom_infinitePlaceCompletion_mul_norm]
    rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, ← pow_mul, ← pow_mul, ← pow_add,
      mul_add]
  rwa [hpf, mul_one] at key

end LocalIndex

universe u

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem FirstInequality.comap_sUnitsToSIdeles_powerSubgroup (hFI : FirstInequality.{u})
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles S = ⊤) :
    ((powerSubgroup n S ∅).subgroupOf (sIdeles S)).comap (sUnitsToSIdeles S) =
      (powMonoidHom n : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_sUnitsToSIdeles, powerSubgroup,
    mem_localSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨hf, hi, -⟩
    obtain ⟨z, hz⟩ := hFI.exists_pow_eq_of_forall_pow_eq S hS hJ e.2
      (fun v hv ↦ by
        obtain ⟨u, hu⟩ := hf v hv
        refine ⟨(u : v.adicCompletion K), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, finiteProj_diagonal]
        rfl)
      (fun w ↦ by
        obtain ⟨u, hu⟩ := hi w
        refine ⟨(u : w.Completion), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, infiniteProj_diagonal]
        rfl)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at hz
      exact ((e : Kˣ)).ne_zero hz.symm
    set zu : Kˣ := Units.mk0 z hz0
    have hzun : zu ^ n = (e : Kˣ) := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])
    have hzu : zu ∈ S.unit K := by
      intro v hv
      have he : v.valuationOfNeZero (e : Kˣ) = 1 := by
        have h := e.2 v hv
        rw [← valuationOfNeZero_eq] at h
        exact_mod_cast h
      have h1 : v.valuationOfNeZero zu ^ n = 1 := by rw [← map_pow, hzun, he]
      rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 h1).resolve_right (NeZero.ne n),
        WithZero.coe_one]
    exact ⟨⟨zu, hzu⟩, Subtype.ext hzun⟩
  · rintro ⟨f, rfl⟩
    refine ⟨fun v _ ↦ ⟨finiteProj v (diagonal K f), ?_⟩,
      fun w ↦ ⟨infiniteProj w (diagonal K f), ?_⟩, fun v hv ↦ ?_⟩
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · exact (diagonal_mem_sIdeles_iff S _).2 (powMonoidHom n f).2 v (by simpa using hv)

theorem FirstInequality.index_map_powerSubgroup (hFI : FirstInequality.{u})
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K)).index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) := by
  set T : Set (HeightOneSpectrum (𝓞 K)) := (S : Set (HeightOneSpectrum (𝓞 K))) with hT
  set W := (powerSubgroup n T ∅).subgroupOf (sIdeles T)
  have hle : powerSubgroup n T ∅ ≤ sIdeles T := by
    simpa using powerSubgroup_le_sIdeles T ∅ n
  have hmap : W.map (sIdelesToIdeleClassGroup T) =
      (powerSubgroup n T ∅).map (IdeleClassGroup.mk K) := by
    rw [sIdelesToIdeleClassGroup, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hle]
  have hW : W.index = n ^ (2 * (S.card + Fintype.card (InfinitePlace K))) :=
    relIndex_powerSubgroup_empty_eq_pow S hS
  have hE : (W.comap (sUnitsToSIdeles T)).index = n ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [hFI.comap_sUnitsToSIdeles_powerSubgroup T (fun v hv ↦ Finset.mem_coe.2 (hS v hv)) hJ,
      SUnit.index_range_powMonoidHom, add_comm]
    simp [T]
  have h := index_map_mul_index_comap T hJ W
  rw [hmap, hE, hW, two_mul,
    pow_add n (S.card + Fintype.card (InfinitePlace K)) (S.card + Fintype.card (InfinitePlace K))] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos n) _) h

end

end GroundTheory.Global
