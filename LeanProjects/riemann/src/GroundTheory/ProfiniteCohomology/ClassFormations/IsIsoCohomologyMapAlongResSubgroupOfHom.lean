import Mathlib
import GroundTheory.ProfiniteCohomology.ClassFormationDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup K]

section Congr

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep B]

theorem cochainsMapAlong_congr {φ ψ : H →* G} (hφ : Continuous φ) (hψ : Continuous ψ)
    (f : Rep.res φ A ⟶ B) (g : Rep.res ψ A ⟶ B) (h : φ = ψ) (hfg : ∀ a : A, f.hom a = g.hom a) :
    cochainsMapAlong φ hφ f = cochainsMapAlong ψ hψ g := by
  subst h
  have : f = g := by
    ext a
    exact hfg a
  subst this
  rfl

theorem cohomologyMapAlong_congr {φ ψ : H →* G} (hφ : Continuous φ) (hψ : Continuous ψ)
    (f : Rep.res φ A ⟶ B) (g : Rep.res ψ A ⟶ B) (h : φ = ψ) (hfg : ∀ a : A, f.hom a = g.hom a)
    (n : ℕ) : cohomologyMapAlong φ hφ f n = cohomologyMapAlong ψ hψ g n := by
  rw [cohomologyMapAlong, cohomologyMapAlong, cochainsMapAlong_congr hφ hψ f g h hfg]

omit [IsTopologicalGroup H] in

theorem cohomologyMapAlong_eq_id {φ : G →* G} (hφ : Continuous φ) (f : Rep.res φ A ⟶ A)
    (h : φ = MonoidHom.id G) (hf : ∀ a : A, f.hom a = a) (n : ℕ) :
    cohomologyMapAlong φ hφ f n = 𝟙 _ := by
  subst h
  have : f = 𝟙 A := by
    ext a
    exact hf a
  subst this
  exact cohomologyMapAlong_id n

end Congr

section Iso

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep B]

noncomputable def resInvHom (e : H ≃* G) (f : Rep.res e.toMonoidHom A ⟶ B)
    (hf : Function.Bijective f.hom) : Rep.res e.symm.toMonoidHom B ⟶ A :=
  Rep.ofHom
    { toLinearMap := (LinearEquiv.ofBijective f.hom.toLinearMap hf).symm.toLinearMap
      isIntertwining' := fun g => by
        ext b
        set L := LinearEquiv.ofBijective f.hom.toLinearMap hf
        apply L.injective
        have h2 : f.hom (A.ρ (e (e.symm g)) (L.symm b)) = B.ρ (e.symm g) (f.hom (L.symm b)) :=
          LinearMap.congr_fun (f.hom.isIntertwining' (e.symm g)) (L.symm b)
        rw [MulEquiv.apply_symm_apply] at h2
        have h3 : f.hom (L.symm b) = b := L.apply_symm_apply b
        rw [h3] at h2
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply]
        exact h2.symm }

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [IsDiscreteRep A] [IsDiscreteRep B] in
theorem resInvHom_hom_apply (e : H ≃* G) (f : Rep.res e.toMonoidHom A ⟶ B)
    (hf : Function.Bijective f.hom) (b : B) :
    f.hom ((resInvHom e f hf).hom b) = b :=
  (LinearEquiv.ofBijective f.hom.toLinearMap hf).apply_symm_apply b

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [IsDiscreteRep A] [IsDiscreteRep B] in
theorem resInvHom_hom_apply' (e : H ≃* G) (f : Rep.res e.toMonoidHom A ⟶ B)
    (hf : Function.Bijective f.hom) (a : A) :
    (resInvHom e f hf).hom (f.hom a) = a :=
  (LinearEquiv.ofBijective f.hom.toLinearMap hf).symm_apply_apply a

theorem isIso_cohomologyMapAlong_of_mulEquiv (e : H ≃* G) (he : Continuous e.toMonoidHom)
    (he' : Continuous e.symm.toMonoidHom) (f : Rep.res e.toMonoidHom A ⟶ B) (hf : Function.Bijective f.hom)
    (n : ℕ) : IsIso (cohomologyMapAlong e.toMonoidHom he f n) := by
  refine ⟨cohomologyMapAlong e.symm.toMonoidHom he' (resInvHom e f hf) n, ?_, ?_⟩
  · rw [← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_eq_id _ _ (by ext; simp) (fun a => resInvHom_hom_apply' e f hf a) n
  · rw [← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_eq_id _ _ (by ext; simp) (fun b => resInvHom_hom_apply e f hf b) n

end Iso

section ResLE

variable (A : Rep.{u} k G) [IsDiscreteRep A]

@[reassoc]
theorem cohomologyResLE_comp {U V W : Subgroup G} (hVU : V ≤ U) (hWV : W ≤ V) (n : ℕ) :
    cohomologyResLE A hVU n ≫ cohomologyResLE A hWV n = cohomologyResLE A (hWV.trans hVU) n := by
  rw [cohomologyResLE, cohomologyResLE, cohomologyResLE, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ rfl (fun _ => rfl) n

end ResLE

section SubgroupOf

variable {U V : Subgroup G} (h : V ≤ U)

omit [IsTopologicalGroup G] in

theorem continuous_subgroupOfEquivOfLe : Continuous (Subgroup.subgroupOfEquivOfLe h).toMonoidHom :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup G] in

theorem continuous_subgroupOfEquivOfLe_symm :
    Continuous (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

variable (A : Rep.{u} k G)

def resSubgroupOfHom :
    Rep.res (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
        (Rep.res (V.subgroupOf U).subtype (Rep.res U.subtype A)) ⟶ Rep.res V.subtype A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [IsDiscreteRep A]

omit h in

instance isDiscreteRep_res_res (W : Subgroup G) (S : Subgroup W) :
    IsDiscreteRep (Rep.res S.subtype (Rep.res W.subtype A)) :=
  isDiscreteRep_res_subtype _ _

theorem cohomologyResLE_eq_cohomologyRes_comp (n : ℕ) :
    cohomologyResLE A h n = cohomologyRes (Rep.res U.subtype A) (V.subgroupOf U) n ≫
      cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
        (continuous_subgroupOfEquivOfLe_symm h) (resSubgroupOfHom h A) n := by
  rw [cohomologyRes, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

instance isIso_cohomologyMapAlong_resSubgroupOfHom (n : ℕ) :
    IsIso (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
        (continuous_subgroupOfEquivOfLe_symm h) (resSubgroupOfHom h A) n) :=
  isIso_cohomologyMapAlong_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h).symm
    (continuous_subgroupOfEquivOfLe_symm h) (continuous_subgroupOfEquivOfLe h) _
    (show Function.Bijective (id : A → A) from Function.bijective_id) n

theorem cohomologyResLE_apply_eq_zero_iff (n : ℕ) (x : cohomology (Rep.res U.subtype A) n) :
    (cohomologyResLE A h n).hom x = 0 ↔
      (cohomologyRes (Rep.res U.subtype A) (V.subgroupOf U) n).hom x = 0 := by
  rw [cohomologyResLE_eq_cohomologyRes_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hinj : Function.Injective (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
      (continuous_subgroupOfEquivOfLe_symm h) (resSubgroupOfHom h A) n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact ⟨fun hx => hinj (by rw [hx, map_zero]), fun hx => by rw [hx, map_zero]⟩

end SubgroupOf

namespace QZ

theorem mk_nsmul (n : ℕ) (q : ℚ) : mk (n • q) = n • mk q := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, mk_add, ih, succ_nsmul]

theorem mk_zsmul (n : ℤ) (q : ℚ) : mk (n • q) = n • mk q := by
  simp [mk]

theorem nsmul_mk_one_div (n : ℕ) : n • mk (1 / n) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [← mk_nsmul, nsmul_eq_mul, mul_one_div_cancel (by exact_mod_cast hn.ne'), mk_eq_zero_iff]
    exact ⟨1, by simp⟩

theorem addOrderOf_mk_one_div {n : ℕ} (hn : 0 < n) : addOrderOf (mk (1 / n)) = n := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) hn

theorem exists_eq_nsmul_mk_one_div {n : ℕ} (hn : 0 < n) {x : QZ} (hx : n • x = 0) :
    ∃ m : ℕ, x = m • mk (1 / n) := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  obtain ⟨m, -, hm⟩ := (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) (u := x) hn).1 hx
  refine ⟨m, ?_⟩
  rw [← mk_nsmul, ← hm, nsmul_eq_mul, mul_one, mul_one_div]
  rfl

end QZ

namespace PreClassFormation

variable {C : Rep.{u} k G} [IsDiscreteRep C] (F : PreClassFormation C)

theorem resLE_eq_zero_iff {U V : OpenSubgroup G} (h : V ≤ U) (hV : Function.Injective (F.inv V))
    (x : H2Open C U) :
    (cohomologyResLE C (show (V : Subgroup G) ≤ U from h) 2).hom x = 0 ↔
      (V : Subgroup G).relIndex U • F.inv U x = 0 := by
  rw [← F.inv_res U V h x]
  exact ⟨fun hx => by rw [hx, map_zero], fun hx => hV (by rw [hx, map_zero])⟩

end PreClassFormation

namespace ClassFormation

variable {C : Rep.{u} k G} [IsDiscreteRep C] (F : ClassFormation C)

noncomputable def invEquiv (U : OpenSubgroup G) : H2Open C U ≃+ QZ :=
  AddEquiv.ofBijective (F.inv U) (F.inv_bijective U)

@[simp]
theorem invEquiv_apply (U : OpenSubgroup G) (x : H2Open C U) : F.invEquiv U x = F.inv U x :=
  rfl

def toClassFormationAt (P : Set Nat.Primes) : ClassFormationAt P C where
  toPreClassFormation := F.toPreClassFormation
  inv_injective U := (F.inv_bijective U).1
  primaryComponent_le_range U _ _ x _ := (F.inv_bijective U).2 x

end ClassFormation

end GroundTheory.ProfCoh
