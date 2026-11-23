import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

namespace GroundTheory.Global

open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem map_range_powMonoidHom {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.map (e : G →* H) = (powMonoidHom n : H →* H).range := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, by simp [map_pow]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x ^ n, ⟨e.symm x, rfl⟩, by simp [map_pow]⟩

theorem index_range_powMonoidHom_of_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by
  rw [← map_range_powMonoidHom e n, Subgroup.index_map_equiv]

omit [NumberField K] in
open Classical in

theorem index_range_powMonoidHom_infinitePlaceCompletion (w : InfinitePlace K) {n : ℕ}
    (hn : n ≠ 0) :
    (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range.index =
      if w.IsReal ∧ Even n then 2 else 1 := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [index_range_powMonoidHom_of_mulEquiv
      (Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv) n,
      index_range_powMonoidHom_real hn]
    by_cases he : Even n <;> simp [hw, he]
  · rw [index_range_powMonoidHom_of_mulEquiv
      (Units.mapEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv) n,
      index_range_powMonoidHom_complex hn]
    have hw' : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
    simp [hw']

namespace IdeleGroup

@[simp]
theorem finiteProj_infiniteEmbedding (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K)
    (x : (w.Completion)ˣ) : finiteProj v (infiniteEmbedding w x) = 1 :=
  Units.ext rfl

@[simp]
theorem infiniteProj_finiteEmbedding (w : InfinitePlace K) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : infiniteProj w (finiteEmbedding v x) = 1 :=
  Units.ext rfl

theorem infiniteEmbedding_mem_standardOpenSubgroup (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infiniteEmbedding w x ∈ standardOpenSubgroup K := by
  rw [mem_standardOpenSubgroup]
  intro v
  rw [← map_inv]
  simp only [coe_infiniteEmbedding]
  exact ⟨one_mem _, one_mem _⟩

def localSubgroup (S T : Set (HeightOneSpectrum (𝓞 K)))
    (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ) : Subgroup (IdeleGroup K) where
  carrier := {x | (∀ v ∈ S, finiteProj v x ∈ H v) ∧ (∀ w, infiniteProj w x ∈ H' w) ∧
    ∀ v ∉ S ∪ T, ord v x = 0}
  one_mem' := ⟨fun v _ ↦ by rw [map_one]; exact one_mem _, fun w ↦ by rw [map_one]; exact one_mem _,
    fun v _ ↦ ord_one v⟩
  mul_mem' {x y} hx hy := ⟨fun v hv ↦ by rw [map_mul]; exact mul_mem (hx.1 v hv) (hy.1 v hv),
    fun w ↦ by rw [map_mul]; exact mul_mem (hx.2.1 w) (hy.2.1 w),
    fun v hv ↦ by rw [ord_mul, hx.2.2 v hv, hy.2.2 v hv, add_zero]⟩
  inv_mem' {x} hx := ⟨fun v hv ↦ by rw [map_inv]; exact inv_mem (hx.1 v hv),
    fun w ↦ by rw [map_inv]; exact inv_mem (hx.2.1 w),
    fun v hv ↦ by rw [ord_inv, hx.2.2 v hv, neg_zero]⟩

variable (S T : Set (HeightOneSpectrum (𝓞 K)))
  (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
  (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)

theorem mem_localSubgroup {x : IdeleGroup K} :
    x ∈ localSubgroup S T H H' ↔ (∀ v ∈ S, finiteProj v x ∈ H v) ∧
      (∀ w, infiniteProj w x ∈ H' w) ∧ ∀ v ∉ S ∪ T, ord v x = 0 :=
  Iff.rfl

theorem localSubgroup_le_sIdeles : localSubgroup S T H H' ≤ sIdeles (S ∪ T) :=
  fun _ hx ↦ hx.2.2

def localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) →*
      (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) × (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w) :=
  MonoidHom.prod
    (MonoidHom.pi fun v ↦ (QuotientGroup.mk' (H v.1)).comp ((finiteProj v.1).comp (sIdeles _).subtype))
    (MonoidHom.pi fun w ↦ (QuotientGroup.mk' (H' w)).comp ((infiniteProj w).comp (sIdeles _).subtype))

theorem ker_localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (localQuotientMap T H H' S).ker =
      (localSubgroup S T H H').subgroupOf (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_localSubgroup]
  simp only [localQuotientMap, MonoidHom.prod_apply, Prod.mk_eq_one, funext_iff, Pi.one_apply,
    MonoidHom.pi_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.coe_subtype, Subtype.forall, Finset.mem_coe]
  exact ⟨fun h ↦ ⟨h.1, h.2, x.2⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩

theorem localQuotientMap_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (localQuotientMap T H H' S) := by
  classical
  rintro ⟨a, b⟩
  choose α hα using fun v : S ↦ QuotientGroup.mk_surjective (a v)
  choose β hβ using fun w ↦ QuotientGroup.mk_surjective (b w)
  let x : IdeleGroup K := (∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)
  have hx : x ∈ sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) := by
    refine mul_mem (prod_mem fun v _ ↦ ?_) (prod_mem fun w _ ↦ ?_)
    · intro u hu
      exact ord_finiteEmbedding_of_ne (fun h ↦ hu (Or.inl (by rw [h]; exact Finset.mem_coe.2 v.2))) _
    · exact standardOpenSubgroup_le_sIdeles _ (infiniteEmbedding_mem_standardOpenSubgroup w _)
  have hfin : ∀ v : S, finiteProj v.1 x = α v := by
    intro v
    simp only [x, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v (fun u _ hu ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp),
      finiteProj_finiteEmbedding]
  have hinf : ∀ w : InfinitePlace K, infiniteProj w x = β w := by
    intro w
    simp only [x, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single w (fun u _ hu ↦
      infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp),
      infiniteProj_infiniteEmbedding]
  refine ⟨⟨x, hx⟩, Prod.ext (funext fun v ↦ ?_) (funext fun w ↦ ?_)⟩
  · exact (congrArg (QuotientGroup.mk (s := H v.1)) (hfin v)).trans (hα v)
  · exact (congrArg (QuotientGroup.mk (s := H' w)) (hinf w)).trans (hβ w)

theorem relIndex_localSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (localSubgroup S T H H').relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (H v).index) * ∏ w : InfinitePlace K, (H' w).index := by
  have hk := Subgroup.index_ker (G' := (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) ×
    (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w)) (localQuotientMap T H H' S)
  rw [Subgroup.relIndex, ← ker_localQuotientMap, hk,
    MonoidHom.range_eq_top_of_surjective _ (localQuotientMap_surjective T H H' S),
    Subgroup.card_top, Nat.card_prod, Nat.card_pi, Nat.card_pi, ← Finset.prod_coe_sort S]
  rfl

def powerSubgroup (n : ℕ) (S T : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) :=
  localSubgroup S T (fun v ↦ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range)
    (fun w ↦ (powMonoidHom n : (w.Completion)ˣ →* _).range)

theorem powerSubgroup_le_sIdeles (n : ℕ) : powerSubgroup n S T ≤ sIdeles (S ∪ T) :=
  localSubgroup_le_sIdeles S T _ _

theorem relIndex_powerSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S T).relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index :=
  relIndex_localSubgroup T _ _ S

theorem relIndex_powerSubgroup_empty (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S ∅).relIndex (sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index := by
  have h := relIndex_powerSubgroup (K := K) ∅ n S
  rwa [Set.union_empty] at h

end IdeleGroup

end

end GroundTheory.Global
