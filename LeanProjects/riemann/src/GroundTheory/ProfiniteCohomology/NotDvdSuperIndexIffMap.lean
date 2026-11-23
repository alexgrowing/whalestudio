import Mathlib
import GroundTheory.ProfiniteCohomology.OpenNormal
import GroundTheory.ProfiniteCohomology.Supernatural
import GroundTheory.ProfiniteCohomology.OfNatRelIndexSupAntitone
import GroundTheory.ProfiniteCohomology.IsProPGroupSubgroupIffIsPGroupMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Pointwise CategoryTheory

variable {G : Type*} [Group G]

theorem sup_eq_comap_map (H U : Subgroup G) [U.Normal] :
    H ⊔ U = (H.map (QuotientGroup.mk' U)).comap (QuotientGroup.mk' U) := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem index_sup_eq_index_map (H U : Subgroup G) [U.Normal] :
    (H ⊔ U).index = (H.map (QuotientGroup.mk' U)).index := by
  rw [sup_eq_comap_map, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)]

variable [TopologicalSpace G]

noncomputable def quotMap {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    G ⧸ (U : Subgroup G) →* G ⧸ (V : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) (fun _ hx => h hx)

theorem quotMap_comp_mk' {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (quotMap h).comp (QuotientGroup.mk' (U : Subgroup G)) = QuotientGroup.mk' (V : Subgroup G) :=
  rfl

theorem quotMap_surjective {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Function.Surjective (quotMap h) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V : Subgroup G) y
  exact ⟨QuotientGroup.mk' (U : Subgroup G) x, rfl⟩

theorem quotMap_self {U : OpenNormalSubgroup G} (h : U ≤ U) : quotMap h = MonoidHom.id _ :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

theorem quotMap_comp {U V W : OpenNormalSubgroup G} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    (quotMap h₂).comp (quotMap h₁) = quotMap (h₁.trans h₂) :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

theorem map_map_quotMap (H : Subgroup G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (H.map (QuotientGroup.mk' (U : Subgroup G))).map (quotMap h) =
      H.map (QuotientGroup.mk' (V : Subgroup G)) := by
  rw [Subgroup.map_map, quotMap_comp_mk']

def IsProSylow (p : ℕ) (P : Subgroup G) : Prop :=
  IsClosed (P : Set G) ∧ IsProPGroup p P ∧ ¬ Supernatural.ofNat p ∣ superIndex P

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {p : ℕ} [hp : Fact p.Prime]

omit [TotallyDisconnectedSpace G] in

theorem not_dvd_superIndex_iff_map (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ p ∣ (H.map (QuotientGroup.mk' (U : Subgroup G))).index := by
  have h := not_dvd_superIndex_iff (⟨p, hp.out⟩ : Nat.Primes) H
  simp only [index_sup_eq_index_map] at h
  exact h

theorem isProSylow_iff {P : Subgroup G} (hP : IsClosed (P : Set G)) :
    IsProSylow p P ↔ ∀ U : OpenNormalSubgroup G,
      IsPGroup p (P.map (QuotientGroup.mk' (U : Subgroup G))) ∧
        ¬ p ∣ (P.map (QuotientGroup.mk' (U : Subgroup G))).index := by
  rw [IsProSylow, isProPGroup_subgroup_iff_isPGroup_map, not_dvd_superIndex_iff_map, ← forall_and]
  exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩

noncomputable def IsProSylow.toSylow {P : Subgroup G} (hP : IsProSylow p P)
    (U : OpenNormalSubgroup G) : Sylow p (G ⧸ (U : Subgroup G)) :=
  IsPGroup.toSylow (isProPGroup_subgroup_iff_isPGroup_map.mp hP.2.1 U)
    ((not_dvd_superIndex_iff_map P).mp hP.2.2 U)

@[simp] theorem IsProSylow.coe_toSylow {P : Subgroup G} (hP : IsProSylow p P)
    (U : OpenNormalSubgroup G) :
    (hP.toSylow U : Subgroup (G ⧸ (U : Subgroup G))) = P.map (QuotientGroup.mk' (U : Subgroup G)) :=
  rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

noncomputable def sylowSystem (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    OpenNormalSubgroup G ⥤ Type _ where
  obj U := {S : Sylow p (G ⧸ (U : Subgroup G)) //
    H.map (QuotientGroup.mk' (U : Subgroup G)) ≤ (S : Subgroup (G ⧸ (U : Subgroup G)))}
  map {U V} f := ↾fun S => ⟨S.1.mapSurjective (quotMap_surjective (leOfHom f)), by
    rw [Sylow.coe_mapSurjective, ← map_map_quotMap H (leOfHom f)]
    exact Subgroup.map_mono S.2⟩
  map_id U := by
    ext ⟨S, hS⟩ x
    show x ∈ (S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap _) ↔
      x ∈ (S : Subgroup (G ⧸ (U : Subgroup G)))
    rw [quotMap_self, Subgroup.map_id]
  map_comp {U V W} f g := by
    ext ⟨S, hS⟩ x
    show x ∈ (S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap _) ↔
      x ∈ ((S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap (leOfHom f))).map
        (quotMap (leOfHom g))
    rw [Subgroup.map_map, quotMap_comp]

theorem exists_isProSylow_le {H : Subgroup G} (hH : IsProPGroup p H) :
    ∃ P : Subgroup G, IsProSylow p P ∧ H ≤ P := by
  rw [isProPGroup_subgroup_iff_isPGroup_map] at hH
  have hfin : ∀ U, Finite ((sylowSystem p H).obj U) := fun U => by
    have := Sylow.finite_of_finiteIndex (default : Sylow p (G ⧸ (U : Subgroup G)))
    exact Subtype.finite
  have hne : ∀ U, Nonempty ((sylowSystem p H).obj U) := fun U => by
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (hH U)
    exact ⟨⟨S, hS⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system (sylowSystem p H)

  let T : OpenNormalSubgroup G → Subgroup G := fun U =>
    ((s U).1 : Subgroup (G ⧸ (U : Subgroup G))).comap (QuotientGroup.mk' (U : Subgroup G))
  have hc : ∀ {U V : OpenNormalSubgroup G} (h : U ≤ V),
      ((s V).1 : Subgroup (G ⧸ (V : Subgroup G))) =
        ((s U).1 : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap h) := by
    intro U V h
    rw [← hs (homOfLE h)]
    rfl
  have hHT : ∀ U, H ≤ T U := fun U => Subgroup.map_le_iff_le_comap.mp (s U).2
  have hUT : ∀ U : OpenNormalSubgroup G, (U : Subgroup G) ≤ T U := fun U x hx => by
    show QuotientGroup.mk' (U : Subgroup G) x ∈ ((s U).1 : Subgroup _)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hTcl : ∀ U, IsClosed (T U : Set G) := fun U =>
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (hUT U) U.toOpenSubgroup.isOpen)
  have hTmono : ∀ {U V : OpenNormalSubgroup G}, U ≤ V → T U ≤ T V := fun {U V} h x hx => by
    show QuotientGroup.mk' (V : Subgroup G) x ∈ ((s V).1 : Subgroup _)
    rw [hc h]
    exact Subgroup.mem_map_of_mem (quotMap h) hx
  have hTlift : ∀ {U V : OpenNormalSubgroup G}, U ≤ V → ∀ x ∈ T V,
      ∃ y ∈ T U, y⁻¹ * x ∈ (V : Subgroup G) := fun {U V} h x hx => by
    have hx' : QuotientGroup.mk' (V : Subgroup G) x ∈ ((s V).1 : Subgroup _) := hx
    rw [hc h] at hx'
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    exact ⟨y, hz, QuotientGroup.eq.mp hzx⟩
  let P : Subgroup G := ⨅ U, T U
  have hPcl : IsClosed (P : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isClosed_iInter hTcl
  have hPmap : ∀ U : OpenNormalSubgroup G,
      P.map (QuotientGroup.mk' (U : Subgroup G)) = ((s U).1 : Subgroup _) := by
    intro U
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr (iInf_le T U)) fun z hz => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    have hx : x ∈ T U := hz

    let t : OpenNormalSubgroup G → Set G := fun W =>
      (T (W ⊓ U) : Set G) ∩ {y | x⁻¹ * y ∈ (U : Subgroup G)}
    have htcl : ∀ W, IsClosed (t W) := fun W =>
      (hTcl _).inter ((Subgroup.isClosed_of_isOpen _ U.toOpenSubgroup.isOpen).preimage
        (continuous_const_mul x⁻¹))
    have htdir : Directed (· ⊇ ·) t := fun W₁ W₂ =>
      ⟨W₁ ⊓ W₂, fun y hy => ⟨hTmono (inf_le_inf_right U inf_le_left) hy.1, hy.2⟩,
        fun y hy => ⟨hTmono (inf_le_inf_right U inf_le_right) hy.1, hy.2⟩⟩
    have htne : ∀ W, (t W).Nonempty := fun W => by
      obtain ⟨y, hy, hyx⟩ := hTlift (inf_le_right : W ⊓ U ≤ U) x hx
      refine ⟨y, hy, ?_⟩
      have := (U : Subgroup G).inv_mem hyx
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htdir
      htne (fun W => (htcl W).isCompact) htcl
    rw [Set.mem_iInter] at hy
    have hyP : y ∈ P := Subgroup.mem_iInf.mpr fun W => hTmono inf_le_left (hy W).1
    refine Subgroup.mem_map.mpr ⟨y, hyP, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq.mpr (hy U).2).symm
  refine ⟨P, (isProSylow_iff hPcl).mpr fun U => ?_, le_iInf fun U => hHT U⟩
  rw [hPmap U]
  exact ⟨(s U).1.isPGroup', (s U).1.not_dvd_index⟩

theorem exists_isProSylow : ∃ P : Subgroup G, IsProSylow p P :=
  let ⟨P, hP, _⟩ := exists_isProSylow_le (isProPGroup_bot (G := G) p)
  ⟨P, hP⟩

end GroundTheory.ProfCoh
