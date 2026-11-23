import Mathlib
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.ColimitUnion
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Closed
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighInfl
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

noncomputable section

section Primary

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

def PrimaryVanishes (ℓ p : ℕ) (M : Rep.{0} k G) [IsDiscreteRep M] : Prop :=
  ∀ (x : cohomology M p) (k : ℕ), ℓ ^ k • x = 0 → x = 0

theorem PrimaryVanishes.of_shortExact {S : ShortComplex (Rep.{0} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : 1 ≤ p)
    (h₁ : PrimaryVanishes ℓ p S.X₁) (h₃ : PrimaryVanishes ℓ p S.X₃) : PrimaryVanishes ℓ p S.X₂ := by
  intro x k hx
  have hg : (cohomologyMap S.g p).hom x = 0 :=
    h₃ _ k (by rw [← map_nsmul, hx, map_zero])
  obtain ⟨y, rfl⟩ := exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero hS p x hg
  obtain ⟨y', ⟨j, hj⟩, hy'⟩ := exists_primary_map_eq (cohomologyMap S.f p).hom.toAddMonoidHom hℓ
    (isTorsion_cohomology _ hp y) (k := k) hx
  have : y' = 0 := h₁ y' j hj
  refine hy'.symm.trans ?_
  change (cohomologyMap S.f p).hom y' = 0
  rw [this, map_zero]

theorem PrimaryVanishes.of_union (M : Rep.{0} k G) [IsDiscreteRep M] {ι : Type} [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι] (W : ι → Submodule k M) (hW : Monotone W)
    (hstable : ∀ i g, W i ≤ (W i).comap (M.ρ g)) (hunion : ∀ a : M, ∃ i, a ∈ W i) {ℓ p : ℕ}
    (hW' : ∀ i (y : cohomology (M.subrepresentation (W i) (hstable i)) p) (k : ℕ), ℓ ^ k • y = 0 →
      ∃ (j : ι) (h : i ≤ j), (cohomologyMap (subrepInclusion M W hW hstable h) p).hom y = 0) :
    PrimaryVanishes ℓ p M := by
  intro x k hx
  obtain ⟨i, y, rfl⟩ := exists_cohomologyMap_subtype_eq M W hW hstable hunion p x
  have hy : (cohomologyMap (Rep.subtype M (W i) (hstable i)) p).hom (ℓ ^ k • y) = 0 := by
    rw [map_nsmul]
    exact hx
  obtain ⟨j, hij, hj⟩ := exists_cohomologyMap_subrepInclusion_eq_zero M W hW hstable hunion p i _ hy
  rw [map_nsmul] at hj
  obtain ⟨l, hjl, hl⟩ := hW' j _ k hj
  have e : subrepInclusion M W hW hstable hij ≫ subrepInclusion M W hW hstable hjl ≫
      Rep.subtype M (W l) (hstable l) = Rep.subtype M (W i) (hstable i) := by
    rw [subrepInclusion_comp_subtype, subrepInclusion_comp_subtype]
  rw [← e, cohomologyMap_comp, cohomologyMap_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, hl, map_zero]

end Primary

section Single

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {H₀ : Type} [Group H₀] (ψ : H₀ →* G)

abbrev divFunRepOne : Rep.{0} (ULift.{0} ℤ) G :=
  divFunRep (I := PUnit) (H := fun _ => H₀) (fun _ => ψ) QZ

def OpenSubgroupAbove (Z : Subgroup G) : Type :=
  {U : OpenSubgroup G // Z ≤ (U : Subgroup G)}

instance (Z : Subgroup G) : Preorder (OpenSubgroupAbove Z) where
  le a b := (b.1 : Subgroup G) ≤ a.1
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := hbc.trans hab

instance (Z : Subgroup G) : Nonempty (OpenSubgroupAbove Z) :=
  ⟨⟨⊤, le_top⟩⟩

instance (Z : Subgroup G) : IsDirectedOrder (OpenSubgroupAbove Z) :=
  ⟨fun a b => ⟨⟨a.1 ⊓ b.1, fun z hz => ⟨a.2 hz, b.2 hz⟩⟩, fun x hx => hx.1, fun x hx => hx.2⟩⟩

abbrev trivQZRes (U : OpenSubgroup G) : Rep.{0} (ULift.{0} ℤ) (U : Subgroup G) :=
  Rep.res (U : Subgroup G).subtype (trivRep G QZ)

instance isDiscreteRep_trivQZRes (U : OpenSubgroup G) : IsDiscreteRep (trivQZRes U) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_coind_trivQZRes (U : OpenSubgroup G) :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (trivQZRes U)) :=
  isDiscreteRep_coind U _

instance isDiscreteRep_res_subtype_trivRepQZ (Z : Subgroup G) :
    IsDiscreteRep (Rep.res Z.subtype (trivRep G QZ)) :=
  isDiscreteRep_res_subtype _ _

def coindToDivFunOne (U : OpenSubgroup G) (hU : ψ.range ≤ (U : Subgroup G)) :
    Rep.coind (U : Subgroup G).subtype (trivQZRes U) ⟶ divFunRepOne ψ :=
  Rep.ofHom ⟨{
      toFun := fun F => ⟨fun _ => F.1, Set.toFinite _, fun _ =>
        ⟨isLocallyConstant_coind U (trivQZRes U) F, fun h x => by
          have := F.2 ⟨ψ h, hU ⟨h, rfl⟩⟩ x
          exact this⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun _ => rfl⟩

theorem coindToDivFunOne_injective (U : OpenSubgroup G) (hU : ψ.range ≤ (U : Subgroup G)) :
    Function.Injective (coindToDivFunOne ψ U hU).hom := fun F F' h =>
  Subtype.ext (congrFun (congrArg Subtype.val h) PUnit.unit)

end Single

section SingleVanish

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {H₀ : Type} [Group H₀] (ψ : H₀ →* G)

def coindIncl {U U' : OpenSubgroup G} (h : (U' : Subgroup G) ≤ U) :
    Rep.coind (U : Subgroup G).subtype (trivQZRes U) ⟶ Rep.coind (U' : Subgroup G).subtype (trivQZRes U') :=
  Rep.ofHom ⟨{
      toFun := fun F => ⟨F.1, fun g x => F.2 ⟨g, h g.2⟩ x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun _ => rfl⟩

theorem cohomologyMap_coindIncl_comp_shapiroMap {U U' : OpenSubgroup G} (h : (U' : Subgroup G) ≤ U) (n : ℕ) :
    cohomologyMap (coindIncl h) n ≫ shapiroMap U' (trivQZRes U') n =
      shapiroMap U (trivQZRes U) n ≫ cohomologyResLE (trivRep G QZ) h n := by
  rw [shapiroMap, shapiroMap, cohomologyResLE, ← cohomologyMapAlong_id_eq_cohomologyMap,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

def divFunOneLevel (a : OpenSubgroupAbove ψ.range) : Submodule (ULift.{0} ℤ) (divFunRepOne ψ) :=
  LinearMap.range (coindToDivFunOne ψ a.1 a.2).hom.toLinearMap

theorem divFunOneLevel_stable (a : OpenSubgroupAbove ψ.range) (g : G) :
    divFunOneLevel ψ a ≤ (divFunOneLevel ψ a).comap ((divFunRepOne ψ).ρ g) :=
  range_repHom_le_comap _ g

instance isDiscreteRep_divFunOneLevel (a : OpenSubgroupAbove ψ.range) :
    IsDiscreteRep ((divFunRepOne ψ).subrepresentation (divFunOneLevel ψ a) (divFunOneLevel_stable ψ a)) :=
  isDiscreteRep_subrepresentation _ _ _

theorem divFunOneLevel_mono : Monotone (divFunOneLevel ψ) := by
  intro a b hab
  rintro _ ⟨F, rfl⟩
  exact ⟨(coindIncl hab).hom F, rfl⟩

omit [TotallyDisconnectedSpace G] in

theorem exists_mem_divFunOneLevel [TotallyDisconnectedSpace G] (f : divFunRepOne ψ) :
    ∃ a, f ∈ divFunOneLevel ψ a := by
  obtain ⟨hlc, hinv⟩ := f.2.2 PUnit.unit
  obtain ⟨V, hV, hVf⟩ := exists_mem_nhds_one_forall_mul_eq hlc
  obtain ⟨W, hWV, hWo, h1W⟩ := mem_nhds_iff.1 hV
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
  let U : OpenSubgroup G := ⟨ψ.range ⊔ (N : Subgroup G), Subgroup.isOpen_mono le_sup_right N.isOpen'⟩
  have hU : ψ.range ≤ (U : Subgroup G) := le_sup_left
  have hF : ∀ (g : (U : Subgroup G)) (x : G), (f : PUnit → G → QZ) PUnit.unit ((U : Subgroup G).subtype g * x) =
      (trivQZRes U).ρ g ((f : PUnit → G → QZ) PUnit.unit x) := by
    intro g x
    obtain ⟨m, ⟨h, rfl⟩, v, hv, hmv⟩ := Subgroup.mem_sup_of_normal_right.1 g.2
    change (f : PUnit → G → QZ) PUnit.unit ((g : G) * x) = (f : PUnit → G → QZ) PUnit.unit x
    have hv' : x⁻¹ * v * x ∈ (N : Subgroup G) := by
      have := Subgroup.Normal.conj_mem inferInstance v hv x⁻¹
      rwa [inv_inv] at this
    rw [← hmv, show ψ h * v * x = ψ h * (x * (x⁻¹ * v * x)) by group, hinv,
      hVf x _ (hWV (hN hv'))]
  refine ⟨⟨U, hU⟩, ⟨⟨(f : PUnit → G → QZ) PUnit.unit, hF⟩, ?_⟩⟩
  apply Subtype.ext
  funext u
  rfl

def coindToDivFunOneLevel (a : OpenSubgroupAbove ψ.range) :
    Rep.coind (a.1 : Subgroup G).subtype (trivQZRes a.1) ⟶
      (divFunRepOne ψ).subrepresentation (divFunOneLevel ψ a) (divFunOneLevel_stable ψ a) :=
  Rep.ofHom ⟨LinearMap.codRestrict (divFunOneLevel ψ a) (coindToDivFunOne ψ a.1 a.2).hom.toLinearMap
      (fun F => ⟨F, rfl⟩), fun _ => rfl⟩

theorem coindToDivFunOneLevel_bijective (a : OpenSubgroupAbove ψ.range) :
    Function.Bijective (coindToDivFunOneLevel ψ a).hom :=
  ⟨fun F F' h => coindToDivFunOne_injective ψ a.1 a.2 (congrArg Subtype.val h), fun y => by
    obtain ⟨F, hF⟩ := y.2
    exact ⟨F, Subtype.ext hF⟩⟩

instance isIso_coindToDivFunOneLevel (a : OpenSubgroupAbove ψ.range) :
    IsIso (coindToDivFunOneLevel ψ a) := by
  have : Mono (coindToDivFunOneLevel ψ a) :=
    (Rep.mono_iff_injective _).2 (coindToDivFunOneLevel_bijective ψ a).1
  have : Epi (coindToDivFunOneLevel ψ a) :=
    (Rep.epi_iff_surjective _).2 (coindToDivFunOneLevel_bijective ψ a).2
  exact isIso_of_mono_of_epi _

theorem coindToDivFunOneLevel_comp_subrepInclusion {a b : OpenSubgroupAbove ψ.range} (hab : a ≤ b) :
    coindToDivFunOneLevel ψ a ≫ subrepInclusion _ _ (divFunOneLevel_mono ψ) (divFunOneLevel_stable ψ) hab =
      coindIncl hab ≫ coindToDivFunOneLevel ψ b :=
  rfl

theorem bijective_cohomologyMap_of_isIso {k : Type} [CommRing k] {A B : Rep.{0} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (f : A ⟶ B) [IsIso f] (n : ℕ) : Function.Bijective (cohomologyMap f n).hom := by
  have : IsIso (cohomologyMap f n) :=
    ⟨cohomologyMap (inv f) n, by rw [← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id],
      by rw [← cohomologyMap_comp, IsIso.inv_hom_id, cohomologyMap_id]⟩
  exact ⟨(ModuleCat.mono_iff_injective _).1 inferInstance, (ModuleCat.epi_iff_surjective _).1 inferInstance⟩

theorem primaryVanishes_divFunRepOne (hZ : IsClosed (ψ.range : Set G)) {ℓ p : ℕ} (hp : 1 ≤ p)
    (hloc : ∀ x : cohomology (Rep.res ψ.range.subtype (trivRep G QZ)) p, (∃ k : ℕ, ℓ ^ k • x = 0) → x = 0) :
    PrimaryVanishes ℓ p (divFunRepOne ψ) := by
  refine PrimaryVanishes.of_union (divFunRepOne ψ) (divFunOneLevel ψ) (divFunOneLevel_mono ψ)
    (divFunOneLevel_stable ψ) (exists_mem_divFunOneLevel ψ) fun a y k hy => ?_
  obtain ⟨x, rfl⟩ := (bijective_cohomologyMap_of_isIso (coindToDivFunOneLevel ψ a) p).2 y
  have hx : ℓ ^ k • x = 0 := (bijective_cohomologyMap_of_isIso (coindToDivFunOneLevel ψ a) p).1
    (by rw [map_nsmul, hy, map_zero])
  set z := (shapiroMap a.1 (trivQZRes a.1) p).hom x with hzdef
  have hz : ℓ ^ k • z = 0 := by rw [hzdef, ← map_nsmul, hx, map_zero]
  have hw : (cohomologyResLE (trivRep G QZ) a.2 p).hom z = 0 :=
    hloc _ ⟨k, by rw [← map_nsmul, hz, map_zero]⟩
  rw [cohomologyResLE_apply_eq_zero_iff] at hw
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hZc : IsClosed ((ψ.range.subgroupOf (a.1 : Subgroup G) : Subgroup (a.1 : Subgroup G)) :
      Set (a.1 : Subgroup G)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hZ.preimage continuous_subtype_val
  obtain ⟨U₀, hU₀o, hZU₀, hU₀⟩ := exists_cohomologyRes_eq_zero (M := trivQZRes a.1) hZc q z hw
  have hopen : IsOpen ((U₀.map (a.1 : Subgroup G).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact (a.1.isOpen).isOpenMap_subtype_val _ hU₀o
  let U' : OpenSubgroup G := ⟨U₀.map (a.1 : Subgroup G).subtype, hopen⟩
  have hU'a : (U' : Subgroup G) ≤ a.1 := Subgroup.map_subtype_le U₀
  have hZU' : ψ.range ≤ (U' : Subgroup G) := fun z hz =>
    ⟨⟨z, a.2 hz⟩, hZU₀ (show (⟨z, a.2 hz⟩ : (a.1 : Subgroup G)) ∈ ψ.range.subgroupOf (a.1 : Subgroup G) from hz), rfl⟩
  let b : OpenSubgroupAbove ψ.range := ⟨U', hZU'⟩
  have hab : a ≤ b := hU'a
  have : IsDiscreteRep (Rep.coind (b.1 : Subgroup G).subtype (trivQZRes b.1)) :=
    isDiscreteRep_coind_trivQZRes b.1
  have hres : (cohomologyResLE (trivRep G QZ) hU'a (q + 1)).hom z = 0 := by
    rw [cohomologyResLE_apply_eq_zero_iff]
    have e : (U' : Subgroup G).subgroupOf (a.1 : Subgroup G) = U₀ :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) U₀
    rw [e]
    exact hU₀
  have hsh : (shapiroMap b.1 (trivQZRes b.1) (q + 1)).hom ((cohomologyMap (coindIncl hab) (q + 1)).hom x) = 0 := by
    have := congrArg (fun φ => φ.hom x) (cohomologyMap_coindIncl_comp_shapiroMap hab (q + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]
    exact hres
  have hinj : Function.Injective (shapiroMap b.1 (trivQZRes b.1) (q + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h0 : (cohomologyMap (coindIncl hab) (q + 1)).hom x = 0 := hinj (hsh.trans (map_zero _).symm)
  refine ⟨b, hab, ?_⟩
  calc (cohomologyMap (subrepInclusion _ _ (divFunOneLevel_mono ψ) (divFunOneLevel_stable ψ) hab) (q + 1)).hom
        ((cohomologyMap (coindToDivFunOneLevel ψ a) (q + 1)).hom x)
      = (cohomologyMap (coindToDivFunOneLevel ψ a ≫
          subrepInclusion _ _ (divFunOneLevel_mono ψ) (divFunOneLevel_stable ψ) hab) (q + 1)).hom x := by
        rw [cohomologyMap_comp]
        rfl
    _ = (cohomologyMap (coindIncl hab ≫ coindToDivFunOneLevel ψ b) (q + 1)).hom x := by
        rw [coindToDivFunOneLevel_comp_subrepInclusion]
    _ = 0 := by
        rw [cohomologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h0, map_zero]

end SingleVanish

section Family

attribute [local instance] Classical.propDecidable

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {I : Type} {H : I → Type} [∀ i, Group (H i)] (φ : ∀ i, H i →* G)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem ker_repHom_le_comap {k : Type} [CommRing k] {A B : Rep.{0} k G} (f : A ⟶ B) (g : G) :
    LinearMap.ker f.hom.toLinearMap ≤ (LinearMap.ker f.hom.toLinearMap).comap (A.ρ g) := by
  intro a ha
  change f.hom (A.ρ g a) = 0
  rw [Rep.hom_comm_apply]
  change B.ρ g (f.hom a) = 0
  rw [show f.hom a = 0 from ha, map_zero]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem mem_divFun_ite (T : Finset I) (f : divFun φ QZ) :
    (fun i => if i ∈ T then 0 else (f : I → G → QZ) i) ∈ divFun φ QZ := by
  refine ⟨f.2.1.subset fun i hi => ?_, fun i => ?_⟩
  · intro hc
    apply hi
    simp only [hc, ite_self]
  · by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact ⟨IsLocallyConstant.const 0, fun _ _ => rfl⟩
    · simp only [hi, if_false]
      exact f.2.2 i

def divFunOutside (T : Finset I) : divFunRep φ QZ ⟶ divFunRep φ QZ :=
  Rep.ofHom ⟨{
      toFun := fun f => ⟨_, mem_divFun_ite φ T f⟩
      map_add' := fun f f' => by
        apply Subtype.ext
        funext i x
        by_cases hi : i ∈ T
        · simp [hi]
        · simp [hi]
      map_smul' := fun c f => by
        apply Subtype.ext
        funext i x
        by_cases hi : i ∈ T
        · simp [hi]
        · simp [hi] }, fun g => by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext i x
    show ((if i ∈ T then 0 else ((divFunAction φ QZ g f : divFun φ QZ) : I → G → QZ) i) : G → QZ) x =
      (if i ∈ T then (0 : G → QZ) else (f : I → G → QZ) i) (x * g)
    by_cases hi : i ∈ T
    · simp [hi]
    · simp [hi, coe_divFunAction_apply]⟩

def divFunSupp (T : Finset I) : Submodule (ULift.{0} ℤ) (divFunRep φ QZ) :=
  LinearMap.ker (divFunOutside φ T).hom.toLinearMap

theorem mem_divFunSupp_iff (T : Finset I) (f : divFunRep φ QZ) :
    f ∈ divFunSupp φ T ↔ ∀ i, i ∉ T → (f.1 : I → G → QZ) i = 0 := by
  constructor
  · intro hf i hi
    have := congrFun (congrArg Subtype.val (show (divFunOutside φ T).hom f = 0 from hf)) i
    simpa [divFunOutside, hi] using this
  · intro hf
    apply Subtype.ext
    funext i
    change (if i ∈ T then 0 else (f : I → G → QZ) i) = 0
    by_cases hi : i ∈ T
    · simp [hi]
    · simp [hi, hf i hi]

theorem divFunSupp_stable (T : Finset I) (g : G) :
    divFunSupp φ T ≤ (divFunSupp φ T).comap ((divFunRep φ QZ).ρ g) :=
  ker_repHom_le_comap _ g

instance isDiscreteRep_divFunSupp (T : Finset I) :
    IsDiscreteRep ((divFunRep φ QZ).subrepresentation (divFunSupp φ T) (divFunSupp_stable φ T)) :=
  isDiscreteRep_subrepresentation _ _ _

theorem divFunSupp_mono : Monotone (divFunSupp φ) := fun T T' h f hf =>
  (mem_divFunSupp_iff φ T' f).2 fun i hi => (mem_divFunSupp_iff φ T f).1 hf i fun hiT => hi (h hiT)

def divFunSuppComponent (T : Finset I) (j : I) :
    (divFunRep φ QZ).subrepresentation (divFunSupp φ (insert j T)) (divFunSupp_stable φ _) ⟶
      divFunRepOne (φ j) :=
  Rep.ofHom ⟨{
      toFun := fun f => ⟨fun _ => ((f.1 : divFun φ QZ) : I → G → QZ) j, Set.toFinite _, fun _ => f.1.2.2 j⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun _ => rfl⟩

def divFunSuppSequence (T : Finset I) (j : I) (hj : j ∉ T) : ShortComplex (Rep.{0} (ULift.{0} ℤ) G) :=
  ShortComplex.mk (subrepInclusion (divFunRep φ QZ) (divFunSupp φ) (divFunSupp_mono φ) (divFunSupp_stable φ)
      (Finset.subset_insert j T)) (divFunSuppComponent φ T j) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext _ x
    exact congrFun ((mem_divFunSupp_iff φ T f.1).1 f.2 j hj) x)

instance isDiscreteRep_divFunSuppSequence_X₁ (T : Finset I) (j : I) (hj : j ∉ T) :
    IsDiscreteRep (divFunSuppSequence φ T j hj).X₁ :=
  isDiscreteRep_divFunSupp φ T

instance isDiscreteRep_divFunSuppSequence_X₂ (T : Finset I) (j : I) (hj : j ∉ T) :
    IsDiscreteRep (divFunSuppSequence φ T j hj).X₂ :=
  isDiscreteRep_divFunSupp φ (insert j T)

instance isDiscreteRep_divFunSuppSequence_X₃ (T : Finset I) (j : I) (hj : j ∉ T) :
    IsDiscreteRep (divFunSuppSequence φ T j hj).X₃ :=
  (inferInstance : IsDiscreteRep (divFunRepOne (φ j)))

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem single_mem_divFun (j : I) (F : G → QZ) (hF : IsLocallyConstant F ∧ ∀ (h : H j) (x : G), F (φ j h * x) = F x) :
    (Pi.single j F : I → G → QZ) ∈ divFun φ QZ := by
  refine ⟨(Set.finite_singleton j).subset fun i hi => ?_, fun i => ?_⟩
  · by_contra h
    have h' : i ≠ j := fun e => h (Set.mem_singleton_iff.2 e)
    exact hi (by simp [Pi.single_apply, h'])
  · by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same]
      exact hF
    · simp only [Pi.single_eq_of_ne h]
      exact ⟨IsLocallyConstant.const 0, fun _ _ => rfl⟩

theorem divFunSuppSequence_shortExact (T : Finset I) (j : I) (hj : j ∉ T) :
    (divFunSuppSequence φ T j hj).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro f hf
    have hj0 : ((f.1 : divFun φ QZ) : I → G → QZ) j = 0 := congrFun (congrArg Subtype.val hf) PUnit.unit
    refine ⟨⟨f.1, (mem_divFunSupp_iff φ T f.1).2 fun i hi => ?_⟩, rfl⟩
    by_cases hij : i = j
    · subst hij
      exact hj0
    · exact (mem_divFunSupp_iff φ _ f.1).1 f.2 i (by simp [hij, hi])
  mono_f := (Rep.mono_iff_injective _).2 fun a b h => Subtype.ext (by
    have h' := congrArg Subtype.val h
    exact h')
  epi_g := (Rep.epi_iff_surjective _).2 fun e => by
    refine ⟨⟨⟨Pi.single j ((e.1 : PUnit → G → QZ) PUnit.unit),
      single_mem_divFun φ j _ (e.2.2 PUnit.unit)⟩, (mem_divFunSupp_iff φ _ _).2 fun i hi => ?_⟩, ?_⟩
    · have hij : i ≠ j := fun h => hi (h ▸ Finset.mem_insert_self j T)
      change (Pi.single j ((e.1 : PUnit → G → QZ) PUnit.unit) : I → G → QZ) i = 0
      simp [Pi.single_apply, hij]
    · apply Subtype.ext
      funext u
      exact Pi.single_eq_same j _

theorem primaryVanishes_divFunSupp (hZ : ∀ i, IsClosed ((φ i).range : Set G)) {ℓ p : ℕ} (hℓ : ℓ.Prime)
    (hp : 1 ≤ p)
    (hloc : ∀ i (x : cohomology (Rep.res (φ i).range.subtype (trivRep G QZ)) p), (∃ k : ℕ, ℓ ^ k • x = 0) → x = 0)
    (T : Finset I) :
    PrimaryVanishes ℓ p ((divFunRep φ QZ).subrepresentation (divFunSupp φ T) (divFunSupp_stable φ T)) := by
  induction T using Finset.induction_on with
  | empty =>
    have : Subsingleton ((divFunRep φ QZ).subrepresentation (divFunSupp φ ∅) (divFunSupp_stable φ ∅)) :=
      ⟨fun a b => Subtype.ext (Subtype.ext (funext fun i =>
        ((mem_divFunSupp_iff φ ∅ a.1).1 a.2 i (by simp)).trans
          ((mem_divFunSupp_iff φ ∅ b.1).1 b.2 i (by simp)).symm))⟩
    intro x k hx
    have := subsingleton_cohomology_of_subsingleton
      ((divFunRep φ QZ).subrepresentation (divFunSupp φ ∅) (divFunSupp_stable φ ∅)) p
    exact Subsingleton.elim _ _
  | insert j T hj ih =>
    exact PrimaryVanishes.of_shortExact (divFunSuppSequence_shortExact φ T j hj) hℓ hp ih
      (primaryVanishes_divFunRepOne (φ j) (hZ j) hp (hloc j))

theorem eq_zero_of_pow_nsmul_cohomology_divFunRep' (hZ : ∀ i, IsClosed ((φ i).range : Set G)) {ℓ : ℕ}
    (hℓ : ℓ.Prime) {p : ℕ} (hp : 1 ≤ p)
    (hloc : ∀ i (x : cohomology (Rep.res (φ i).range.subtype (trivRep G QZ)) p), (∃ k : ℕ, ℓ ^ k • x = 0) → x = 0)
    (x : cohomology (divFunRep φ QZ) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  refine PrimaryVanishes.of_union (divFunRep φ QZ) (divFunSupp φ) (divFunSupp_mono φ) (divFunSupp_stable φ)
    (fun a => ⟨a.2.1.toFinset, (mem_divFunSupp_iff φ _ a).2 fun i hi => ?_⟩)
    (fun T y k hy => ⟨T, le_rfl, ?_⟩) x k hx
  · by_contra h
    exact hi (a.2.1.mem_toFinset.2 h)
  · rw [primaryVanishes_divFunSupp φ hZ hℓ hp hloc T y k hy, map_zero]

theorem eq_zero_of_pow_nsmul_cohomology_divFunRep [T2Space G] [∀ i, TopologicalSpace (H i)]
    [∀ i, CompactSpace (H i)] (hφ : ∀ i, Continuous (φ i)) {ℓ : ℕ} (hℓ : ℓ.Prime) {p : ℕ} (hp : 1 ≤ p)
    (hloc : ∀ i (x : cohomology (Rep.res (φ i).range.subtype (trivRep G QZ)) p), (∃ k : ℕ, ℓ ^ k • x = 0) → x = 0)
    (x : cohomology (divFunRep φ QZ) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 :=
  eq_zero_of_pow_nsmul_cohomology_divFunRep' φ (fun i => by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (hφ i)).isClosed) hℓ hp hloc x k hx

end Family

end

end GroundTheory.ProfCoh
