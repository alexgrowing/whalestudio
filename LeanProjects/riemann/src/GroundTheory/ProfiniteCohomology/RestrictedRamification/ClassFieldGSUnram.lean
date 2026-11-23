import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.GlobalFields.ClassFieldConsequences.Conductor
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import GroundTheory.GlobalFields.KummerTheory.Splitting
import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal Function

noncomputable section

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

open Classical in

theorem finiteProj_prod_finiteEmbedding (T : Finset (HeightOneSpectrum (𝓞 K)))
    (b : ∀ u : HeightOneSpectrum (𝓞 K), (u.adicCompletion K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteProj v (∏ u ∈ T, finiteEmbedding u (b u)) = if v ∈ T then b v else 1 := by
  rw [map_prod]
  split_ifs with hv
  · rw [Finset.prod_eq_single v (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (Ne.symm hu) _)
      (fun h ↦ absurd hv h), finiteProj_finiteEmbedding]
  · exact Finset.prod_eq_one fun u hu ↦ finiteProj_finiteEmbedding_of_ne (by rintro rfl; exact hv hu) _

theorem infiniteProj_prod_finiteEmbedding (T : Finset (HeightOneSpectrum (𝓞 K)))
    (b : ∀ u : HeightOneSpectrum (𝓞 K), (u.adicCompletion K)ˣ) (w : InfinitePlace K) :
    infiniteProj w (∏ u ∈ T, finiteEmbedding u (b u)) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one fun u _ ↦ infiniteProj_finiteEmbedding w u _

section Symbol

variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

theorem exponent_conductor_eq_zero {v : HeightOneSpectrum (𝓞 K)}
    (h : ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (Modulus.conductor K L).exponent v = 0 := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  rw [Modulus.exponent_conductor, localConductorExponent_eq_zero_iff L v w.1]
  exact h w

theorem unitsOutsidePos_le_ker_ideleSymbol
    (h : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    unitsOutsidePos S ≤ (ideleSymbol K L).ker := by
  refine le_trans (fun x hx ↦ ?_)
    ((Modulus.congruenceSubgroup_le_ker_ideleSymbol_iff (L := L) _).2 (Modulus.dvd_refl' _))
  obtain ⟨hx, hpos⟩ := mem_unitsOutsidePos.1 hx
  obtain ⟨hS, hout⟩ := mem_unitsOutside.1 hx
  refine (Modulus.mem_congruenceSubgroup _).2 ⟨fun v ↦ ?_, fun w _ ↦ hpos w⟩
  by_cases hv : v ∈ S
  · rw [hS v hv]
    exact one_mem _
  · rw [exponent_conductor_eq_zero L (h v hv)]
    exact hout v hv

end Symbol

section Field

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem ramificationIdx_eq_one_of_isUnramifiedOutside {E : IntermediateField K Ω} [FiniteDimensional K E]
    (hE : IsUnramifiedOutside S E) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (w : PlacesOver E v) :
    w.1.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have := NumberField.of_module_finite K E
  exact Algebra.IsUnramifiedIn.ramificationIdx_eq_one (hE v hv) w.2

theorem isUnramifiedOutside_of_ramificationIdx_eq_one {E : IntermediateField K Ω} [FiniteDimensional K E]
    (h : ∀ v ∉ S, ∀ w : PlacesOver E v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    IsUnramifiedOutside S E := by
  have := NumberField.of_module_finite K E
  intro v hv
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P _ hP
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  exact h v hv ⟨⟨P, inferInstance, hP0⟩, hP⟩

theorem unitsOutsidePos_le_ker_ideleSymbol_of_isUnramifiedOutside (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsAbelianGalois K E] (hE : IsUnramifiedOutside S E) :
    unitsOutsidePos S ≤ (ideleSymbol K E).ker :=
  unitsOutsidePos_le_ker_ideleSymbol S E fun _ hv w ↦
    ramificationIdx_eq_one_of_isUnramifiedOutside S hE hv w

end Field

theorem exists_modulus_congruenceSubgroup_le (hS : S.Finite) {n : ℕ} (hn : n ≠ 0) :
    ∃ 𝔪 : Modulus K, (∀ v ∉ S, 𝔪.exponent v = 0) ∧
      𝔪.congruenceSubgroup ≤ (powMonoidHom n : IdeleGroup K →* IdeleGroup K).range ⊔ unitsOutsidePos S := by
  classical
  have hk : ∀ v : HeightOneSpectrum (𝓞 K), ∃ k : ℕ, (unitsLevel (K := K) v k : Set (v.adicCompletion K)ˣ) ⊆
      ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range : Set (v.adicCompletion K)ˣ) := fun v ↦ by
    obtain ⟨k, -, hk⟩ := exists_unitsLevel_subset v
      ((isOpen_range_powMonoidHom_adicCompletion v hn).mem_nhds (one_mem _))
    exact ⟨k, hk⟩
  choose k hk using hk
  let a : HeightOneSpectrum (𝓞 K) → ℕ := fun v ↦ if v ∈ S then k v else 0
  have ha : (support a).Finite := hS.subset fun v hv ↦ by
    by_contra h
    exact hv (if_neg h)
  let 𝔪 : Modulus K := ⟨∏ᶠ w, w.asIdeal ^ a w, finprod_asIdeal_pow_ne_bot a, Set.univ⟩
  have hexp : ∀ v, 𝔪.exponent v = a v := fun v ↦ multiplicity_finprod_asIdeal_pow_eq ha v
  refine ⟨𝔪, fun v hv ↦ by rw [hexp]; exact if_neg hv, fun x hx ↦ ?_⟩
  obtain ⟨hf, hr⟩ := (Modulus.mem_congruenceSubgroup _).1 hx
  set T := hS.toFinset
  set p : IdeleGroup K := ∏ u ∈ T, finiteEmbedding u (finiteProj u x) with hp
  have hpP : p ∈ (powMonoidHom n : IdeleGroup K →* IdeleGroup K).range := by
    refine Subgroup.prod_mem _ fun u hu ↦ ?_
    have hu' : u ∈ S := hS.mem_toFinset.1 hu
    have hmem := hf u
    rw [hexp u, show a u = k u from if_pos hu'] at hmem
    obtain ⟨z, hz⟩ := hk u hmem
    exact ⟨finiteEmbedding u z, by rw [powMonoidHom_apply, ← map_pow, ← powMonoidHom_apply, hz]⟩
  have hrest : p⁻¹ * x ∈ unitsOutsidePos S := by
    refine mem_unitsOutsidePos.2 ⟨mem_unitsOutside.2 ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩, fun w ↦ ?_⟩
    · rw [map_mul, map_inv, hp, finiteProj_prod_finiteEmbedding, if_pos (hS.mem_toFinset.2 hv),
        inv_mul_cancel]
    · rw [map_mul, map_inv, hp, finiteProj_prod_finiteEmbedding,
        if_neg (fun h ↦ hv (hS.mem_toFinset.1 h)), inv_one, one_mul]
      exact unitsLevel_antitone v (Nat.zero_le _) (hf v)
    · rw [map_mul, map_inv, hp, infiniteProj_prod_finiteEmbedding, inv_one, one_mul]
      exact hr w (Set.mem_univ _)
  have : x = p * (p⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hpP hrest

variable {S}

theorem exists_modulus_map_congruenceSubgroup_le (hS : S.Finite) {n : ℕ} (hn : n ≠ 0)
    (N : Subgroup (IdeleClassGroup K)) (hpow : ∀ c : IdeleClassGroup K, c ^ n ∈ N)
    (hU : ∀ x ∈ unitsOutsidePos S, IdeleClassGroup.mk K x ∈ N) :
    ∃ 𝔪 : Modulus K, (∀ v ∉ S, 𝔪.exponent v = 0) ∧
      𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ N := by
  obtain ⟨𝔪, h0, hle⟩ := exists_modulus_congruenceSubgroup_le S hS hn
  refine ⟨𝔪, h0, Subgroup.map_le_iff_le_comap.2 (hle.trans (sup_le ?_ fun x hx ↦ hU x hx))⟩
  rintro _ ⟨y, rfl⟩
  change IdeleClassGroup.mk K (y ^ n) ∈ N
  rw [map_pow]
  exact hpow _

theorem isOpen_of_pow_mem_of_unitsOutsidePos (hS : S.Finite) {n : ℕ} (hn : n ≠ 0)
    (N : Subgroup (IdeleClassGroup K)) (hpow : ∀ c : IdeleClassGroup K, c ^ n ∈ N)
    (hU : ∀ x ∈ unitsOutsidePos S, IdeleClassGroup.mk K x ∈ N) :
    IsOpen (N : Set (IdeleClassGroup K)) := by
  obtain ⟨𝔪, -, hle⟩ := exists_modulus_map_congruenceSubgroup_le hS hn N hpow hU
  exact Subgroup.isOpen_mono hle 𝔪.isOpen_map_congruenceSubgroup

theorem finiteIndex_of_pow_mem_of_unitsOutsidePos (hS : S.Finite) {n : ℕ} (hn : n ≠ 0)
    (N : Subgroup (IdeleClassGroup K)) (hpow : ∀ c : IdeleClassGroup K, c ^ n ∈ N)
    (hU : ∀ x ∈ unitsOutsidePos S, IdeleClassGroup.mk K x ∈ N) :
    N.FiniteIndex := by
  obtain ⟨𝔪, -, hle⟩ := exists_modulus_map_congruenceSubgroup_le hS hn N hpow hU
  have := 𝔪.finiteIndex_map_congruenceSubgroup
  exact Subgroup.finiteIndex_of_le hle

theorem isUnramifiedOutside_of_range_ideleClassNorm {Ω : Type*} [Field Ω] [Algebra K Ω] (hS : S.Finite)
    {n : ℕ} (hn : n ≠ 0) (E : IntermediateField K Ω) [FiniteDimensional K E] [IsAbelianGalois K E]
    (hpow : ∀ c : IdeleClassGroup K, c ^ n ∈ (ideleClassNorm K E).range)
    (hU : ∀ x ∈ unitsOutsidePos S, IdeleClassGroup.mk K x ∈ (ideleClassNorm K E).range) :
    IsUnramifiedOutside S E := by
  obtain ⟨𝔪, h0, hle⟩ := exists_modulus_map_congruenceSubgroup_le hS hn _ hpow hU
  have hdvd := (Modulus.map_congruenceSubgroup_le_range_ideleClassNorm_iff (L := E) 𝔪).1 hle
  have hexp := (Modulus.ideal_dvd_ideal_iff.1 (Modulus.dvd_iff.1 hdvd).1)
  refine isUnramifiedOutside_of_ramificationIdx_eq_one S fun v hv w ↦ ?_
  have h1 : (Modulus.conductor K E).exponent v = 0 := by
    have := hexp v
    rw [h0 v hv] at this
    omega
  rw [Modulus.exponent_conductor] at h1
  exact (localConductorExponent_eq_zero_iff E v w.1).1 h1

end

end GroundTheory.ProfCoh
