import Mathlib
import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.PowerKernel
import GroundTheory.GlobalFields.ExistenceTheorem.IndexRangePowMonoidHomAdicCompletionMulNorm

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh IdeleGroup

namespace KummerIndex

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

theorem mem_unit_of_pow_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} (hp : p ≠ 0) {b : Kˣ}
    (hb : b ^ p ∈ S.unit K) : b ∈ S.unit K := by
  intro v hv
  have he : v.valuationOfNeZero (b ^ p) = 1 := by
    have h := hb v hv
    rw [← valuationOfNeZero_eq] at h
    exact_mod_cast h
  rw [map_pow] at he
  rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 he).resolve_right hp, WithZero.coe_one]

theorem unitsPow_subgroupOf_unit (S : Set (HeightOneSpectrum (𝓞 K))) (hp : p ≠ 0) :
    (unitsPow K p).subgroupOf (S.unit K) = (powMonoidHom p : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, mem_unitsPow]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨b, mem_unit_of_pow_mem_unit hp (hb ▸ e.2)⟩, Subtype.ext ?_⟩
    rw [powMonoidHom_apply, Subgroup.coe_pow]
    exact hb
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem relIndex_powerSubgroup_eq_pow [NeZero p] [HasEnoughRootsOfUnity K p]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) T).relIndex
        (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      p ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  rw [relIndex_powerSubgroup, ← relIndex_powerSubgroup_empty, relIndex_powerSubgroup_empty_eq_pow S hpS]

universe u

variable {K : Type u} [Field K] [NumberField K] [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.GroundTheory.Global.FirstInequality.comap_sUnitsToSIdeles_powerSubgroup_union
    (hFI : FirstInequality.{u}) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    (hsurj : ∀ z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
      (∀ v ∈ T, z v ∈ localUnits v) → ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        ∀ v ∈ T, localClass v p δ = QuotientGroup.mk (z v)) :
    ((powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).subgroupOf
        (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T))).comap
          (sUnitsToSIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (powMonoidHom p : ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K →* _).range := by
  ext e
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_sUnitsToSIdeles, powerSubgroup,
    mem_localSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨hf, hi, -⟩
    have hy := hFI.mem_unitsPow_of_forall_mem_unitsPowIn S T hST hpS hJ hsurj e.2
      (fun v hv ↦ by
        obtain ⟨u, hu⟩ := hf v hv
        refine mem_unitsPowIn.2 ⟨(u : v.adicCompletion K), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, finiteProj_diagonal]
        rfl)
      (fun w ↦ by
        obtain ⟨u, hu⟩ := hi w
        refine mem_unitsPowIn.2 ⟨(u : w.Completion), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, infiniteProj_diagonal]
        rfl)
    obtain ⟨b, hb⟩ := mem_unitsPow.1 hy
    refine ⟨⟨b, mem_unit_of_pow_mem_unit (Fact.out : p.Prime).ne_zero (hb ▸ e.2)⟩,
      Subtype.ext ?_⟩
    rw [powMonoidHom_apply, Subgroup.coe_pow]
    exact hb
  · rintro ⟨f, rfl⟩
    refine ⟨fun v _ ↦ ⟨finiteProj v (diagonal K f), ?_⟩,
      fun w ↦ ⟨infiniteProj w (diagonal K f), ?_⟩, fun v hv ↦ ?_⟩
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · exact (diagonal_mem_sIdeles_iff _ _).2 (powMonoidHom p f).2 v hv

theorem card_add_one_eq (S T : Finset (HeightOneSpectrum (𝓞 K))) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hap : a ∉ unitsPow K p)
    (haT : ∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K))
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) = p ^ T.card)
    (hker : ∀ x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, x ∈ unitsPowAt p T →
      x ∈ radicalGroup K p a) :
    T.card + 1 = S.card + Fintype.card (InfinitePlace K) := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hΔp : (unitsPow K p).relIndex Δ = p ^ (Fintype.card (InfinitePlace K) + S.card) := by
    rw [Subgroup.relIndex, unitsPow_subgroupOf_unit _ (Fact.out : p.Prime).ne_zero,
      SUnit.index_range_powMonoidHom]
    simp
  have heq : radicalGroup K p a ⊓ Δ = unitsPowAt p T ⊓ Δ := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨radicalGroup_le (mem_unitsPowAt.2 haT) (unitsPow_le_unitsPowAt p T) h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hker x h2 h1, h2⟩
  have hrad : (radicalGroup K p a).relIndex Δ = p ^ T.card := by
    rw [← Subgroup.inf_relIndex_right, heq, Subgroup.inf_relIndex_right, hidx]
  have hstep : (unitsPow K p).relIndex (radicalGroup K p a ⊓ Δ) = p := by
    rw [← QuotientGroup.ker_mk' (unitsPow K p), Subgroup.relIndex_ker]
    set H := (radicalGroup K p a ⊓ Δ).map (QuotientGroup.mk' (unitsPow K p))
    have hle : H ≤ Subgroup.zpowers (QuotientGroup.mk' (unitsPow K p) a) := by
      rw [← radicalClasses_radicalGroup]
      exact Subgroup.map_mono inf_le_left
    have hord : orderOf (QuotientGroup.mk' (unitsPow K p) a) = p := by
      refine orderOf_eq_prime (UnitsModPow.pow_eq_one _ _ _) ?_
      rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hdvd : Nat.card H ∣ p := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hord] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hp
    · exfalso
      have hbot := Subgroup.card_eq_one.1 h1
      have hmem : QuotientGroup.mk' (unitsPow K p) a ∈ H :=
        Subgroup.mem_map_of_mem _ ⟨mem_radicalGroup_self a, ha⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hap hmem
    · exact hp
  have h := Subgroup.relIndex_inf_mul_relIndex (unitsPow K p) (radicalGroup K p a) Δ
  rw [inf_of_le_left (unitsPow_le_radicalGroup a), hstep, hrad, hΔp, ← pow_succ'] at h
  have := Nat.pow_right_injective (Fact.out : p.Prime).two_le h
  omega

theorem _root_.GroundTheory.Global.FirstInequality.exists_places_index_map_powerSubgroup
    (hFI : FirstInequality.{u}) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    {a : Kˣ} (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hap : a ∉ unitsPow K p) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      T.card + 1 = S.card + Fintype.card (InfinitePlace K) ∧
      (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
      ((powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).map
        (IdeleClassGroup.mk K)).index = p := by
  classical
  obtain ⟨T, hST, haT, hidx, hker⟩ := hFI.exists_places_unitsPowAt S hpS ha
  have hcard := card_add_one_eq S T ha hap haT hidx hker
  refine ⟨T, hST, hcard, haT, ?_⟩
  have hpT : ∀ v ∈ T, (p : 𝓞 K) ∉ v.asIdeal := fun v hv h ↦
    Finset.disjoint_right.1 hST hv (hpS v h)
  have hsurj := exists_localClass_eq S T hST hpT hidx
  set S' : Set (HeightOneSpectrum (𝓞 K)) := (S : Set (HeightOneSpectrum (𝓞 K))) ∪ T with hS'
  have hJ' : (diagonal K).range ⊔ sIdeles S' = ⊤ :=
    sup_sIdeles_eq_top_of_subset Set.subset_union_left hJ
  set W := (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).subgroupOf
    (sIdeles S')
  have hle : powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))) ≤
      sIdeles S' :=
    powerSubgroup_le_sIdeles _ _ p
  have hmap : W.map (sIdelesToIdeleClassGroup S') =
      (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).map
        (IdeleClassGroup.mk K) := by
    rw [sIdelesToIdeleClassGroup, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hle]
  have hW : W.index = p ^ (2 * (S.card + Fintype.card (InfinitePlace K))) :=
    relIndex_powerSubgroup_eq_pow S T hpS
  have hcardS' : Nat.card S' = S.card + T.card := by
    rw [hS', ← Finset.coe_union, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      Finset.card_union_of_disjoint hST]
  have hE : (W.comap (sUnitsToSIdeles S')).index =
      p ^ (Fintype.card (InfinitePlace K) + (S.card + T.card)) := by
    rw [hFI.comap_sUnitsToSIdeles_powerSubgroup_union S T hST hpS hJ hsurj,
      SUnit.index_range_powMonoidHom, hcardS']
  have h := index_map_mul_index_comap S' hJ' W
  rw [hmap, hE, hW] at h
  have h2 : 2 * (S.card + Fintype.card (InfinitePlace K)) =
      1 + (Fintype.card (InfinitePlace K) + (S.card + T.card)) := by omega
  rw [h2, pow_add p 1, pow_one] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos _) h

end KummerIndex

end GroundTheory.Global
