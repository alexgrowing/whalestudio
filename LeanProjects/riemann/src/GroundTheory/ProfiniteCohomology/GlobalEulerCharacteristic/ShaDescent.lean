import Mathlib
import GroundTheory.ProfiniteCohomology.MackeyFormula.CompactSupport
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.InnerConj
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Descent
import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.DescentMaps
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

noncomputable section

section Sha

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

def shaSubmodule (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) : Submodule k (cohomology A n) where
  carrier := {x | ∀ v, (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) n).hom x = 0}
  add_mem' {x y} hx hy v := by
    change (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) n).hom (x + y) = 0
    rw [map_add, hx v, hy v, add_zero]
  zero_mem' v := map_zero _
  smul_mem' c x hx v := by
    change (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) n).hom (c • x) = 0
    rw [map_smul, hx v, smul_zero]

theorem cohomologyMap_mem_shaSubmodule {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (f : A ⟶ B)
    {n : ℕ} {x : cohomology A n} (hx : x ∈ shaSubmodule φ A n) :
    (cohomologyMap f n).hom x ∈ shaSubmodule φ B n := by
  intro v
  have e1 := cohomologyMapAlong_comp_apply_of_eq (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
    (MonoidHom.id G) continuous_id (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (fun _ => rfl)
    f (𝟙 _) ((Rep.resFunctor (φ v).toMonoidHom).map f) (fun _ => rfl) n x
  rw [cohomologyMapAlong_id_eq_cohomologyMap] at e1
  have e2 := cohomologyMap_cohomologyMapAlong_apply (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
    (𝟙 _) ((Rep.resFunctor (φ v).toMonoidHom).map f) n x
  rw [Category.id_comp] at e2
  rw [e1, ← e2, hx v, map_zero]

theorem mem_ptSha_iff_mem_shaSubmodule (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] {n : ℕ}
    (x : cohomology A n) : x ∈ ptSha φ A n ↔ x ∈ shaSubmodule φ A n := by
  refine ⟨fun hx v => ptRes_eq_zero_of_mem_ptSha φ A hx v, fun hx => ?_⟩
  rw [mem_ptSha]
  funext v
  exact hx v

end Sha

section Nsmul

theorem bijective_nsmul_of_dvd {A : Type*} [AddCommGroup A] {m n : ℕ} (hmn : m ∣ n)
    (hn : Function.Bijective fun a : A => n • a) : Function.Bijective fun a : A => m • a := by
  obtain ⟨c, rfl⟩ := hmn
  refine ⟨fun a b hab => hn.1 ?_, fun a => ?_⟩
  · have hab' : m • a = m • b := hab
    change (m * c) • a = (m * c) • b
    rw [mul_comm, ← smul_smul, ← smul_smul, hab']
  · obtain ⟨b, rfl⟩ := hn.2 a
    exact ⟨c • b, by change m • c • b = (m * c) • b; rw [smul_smul]⟩

end Nsmul

section Instances

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

instance isDiscreteRep_res_subtype_res_toMonoidHom {H' : Type u} [Group H'] [TopologicalSpace H']
    (ψ : H' →ₜ* G) (B : Rep.{u} k G) [IsDiscreteRep B] (S : Subgroup H') :
    IsDiscreteRep (Rep.res S.subtype (Rep.res ψ.toMonoidHom B)) :=
  haveI := IsDiscreteRep.res (continuous_toMonoidHom ψ) B
  IsDiscreteRep.res (continuous_subgroup_subtype S) _

instance isDiscreteRep_res_toMonoidHom_res_subtype {H' : Type u} [Group H'] [TopologicalSpace H']
    (S : Subgroup G) (ψ : H' →ₜ* S) (B : Rep.{u} k G) [IsDiscreteRep B] :
    IsDiscreteRep (Rep.res ψ.toMonoidHom (Rep.res S.subtype B)) :=
  haveI := IsDiscreteRep.res (continuous_subgroup_subtype S) B
  IsDiscreteRep.res (continuous_toMonoidHom ψ) _

end Instances

section Descent

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  (V : OpenSubgroup G) (A : Rep.{u} k G) [IsDiscreteRep A]

def mackeyTranslateMor (p : MackeyIndex V φ) :
    Rep.res (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype
        (Rep.res (φ p.1).toMonoidHom A) ⟶
      Rep.res (mackeyFamily V φ p).toMonoidHom (Rep.res (V : Subgroup G).subtype A) :=
  Rep.ofHom ⟨A.ρ p.2.out, fun h => by
    ext a
    change A.ρ p.2.out (A.ρ ((φ p.1) (h : Hv p.1)) a) =
      A.ρ (p.2.out * (φ p.1) (h : Hv p.1) * p.2.out⁻¹) (A.ρ p.2.out a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

def mackeyTranslateInv (p : MackeyIndex V φ) :
    Rep.res (mackeyFamily V φ p).toMonoidHom (Rep.res (V : Subgroup G).subtype A) ⟶
      Rep.res (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype
        (Rep.res (φ p.1).toMonoidHom A) :=
  Rep.ofHom ⟨A.ρ p.2.out⁻¹, fun h => by
    ext a
    change A.ρ p.2.out⁻¹ (A.ρ (p.2.out * (φ p.1) (h : Hv p.1) * p.2.out⁻¹) a) =
      A.ρ ((φ p.1) (h : Hv p.1)) (A.ρ p.2.out⁻¹ a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

omit [CompactSpace G] [∀ v, CompactSpace (Hv v)] in
theorem cohomologyMap_mackeyTranslateMor_injective (p : MackeyIndex V φ) (n : ℕ) :
    Function.Injective (cohomologyMap (mackeyTranslateMor φ V A p) n).hom := by
  have h : mackeyTranslateMor φ V A p ≫ mackeyTranslateInv φ V A p = 𝟙 _ := by
    ext a
    change A.ρ p.2.out⁻¹ (A.ρ p.2.out a) = a
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine Function.LeftInverse.injective (g := (cohomologyMap (mackeyTranslateInv φ V A p) n).hom) fun z => ?_
  rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, h, cohomologyMap_id]
  rfl

omit [∀ v, CompactSpace (Hv v)] in

theorem cohomologyMapAlong_mackeyFamily_cohomologyRes (p : MackeyIndex V φ) (n : ℕ) (y : cohomology A n) :
    (cohomologyMapAlong (mackeyFamily V φ p).toMonoidHom (continuous_toMonoidHom (mackeyFamily V φ p)) (𝟙 _) n).hom
        ((cohomologyRes A (V : Subgroup G) n).hom y) =
      (cohomologyMap (mackeyTranslateMor φ V A p) n).hom
        ((cohomologyRes (Rep.res (φ p.1).toMonoidHom A)
          (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) n).hom
          ((cohomologyMapAlong (φ p.1).toMonoidHom (continuous_toMonoidHom (φ p.1)) (𝟙 _) n).hom y)) := by
  set x := p.2.out

  let φ' : mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom x →* G :=
    (φ p.1).toMonoidHom.comp (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom x).subtype
  have hφ' : Continuous φ' :=
    (continuous_toMonoidHom (φ p.1)).comp (continuous_subgroup_subtype _)
  let g' : Rep.res φ' A ⟶ Rep.res (mackeyFamily V φ p).toMonoidHom (Rep.res (V : Subgroup G).subtype A) :=
    Rep.ofHom ⟨A.ρ x, fun h => by
      ext a
      change A.ρ x (A.ρ ((φ p.1) (h : Hv p.1)) a) = A.ρ (x * (φ p.1) (h : Hv p.1) * x⁻¹) (A.ρ x a)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group⟩

  let c : (V : Subgroup G) →* G := (innerConjHom x).comp (V : Subgroup G).subtype
  have hc : Continuous c := (continuous_innerConjHom x).comp (continuous_subgroup_subtype _)
  let g₁ : Rep.res c A ⟶ Rep.res (V : Subgroup G).subtype A :=
    Rep.ofHom ⟨A.ρ x, fun h => by
      ext a
      change A.ρ x (A.ρ (x⁻¹ * (h : G) * x) a) = A.ρ (h : G) (A.ρ x a)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group⟩
  have s1 : (cohomologyRes A (V : Subgroup G) n).hom y =
      (cohomologyMapAlong c hc g₁ n).hom y := by
    conv_lhs => rw [← cohomologyInnerConj_apply A n x y]
    exact cohomologyMapAlong_comp_apply_of_eq (V : Subgroup G).subtype (continuous_subgroup_subtype _)
      (innerConjHom x) (continuous_innerConjHom x) c hc (fun _ => rfl) (innerConjMor A x) (𝟙 _) g₁
      (fun _ => rfl) n y
  have s2 := cohomologyMapAlong_comp_apply_of_eq (mackeyFamily V φ p).toMonoidHom
    (continuous_toMonoidHom (mackeyFamily V φ p)) c hc φ' hφ' (fun h => by
      change x⁻¹ * (x * (φ p.1) (h : Hv p.1) * x⁻¹) * x = (φ p.1) (h : Hv p.1)
      group) g₁ (𝟙 _) g' (fun _ => rfl) n y

  have s3 := cohomologyMap_cohomologyMapAlong_apply
    (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom x).subtype (continuous_subgroup_subtype _)
    (𝟙 _) (mackeyTranslateMor φ V A p) n
    ((cohomologyMapAlong (φ p.1).toMonoidHom (continuous_toMonoidHom (φ p.1)) (𝟙 _) n).hom y)
  have s4 := cohomologyMapAlong_comp_apply_of_eq
    (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom x).subtype (continuous_subgroup_subtype _)
    (φ p.1).toMonoidHom (continuous_toMonoidHom (φ p.1)) φ' hφ' (fun _ => rfl) (𝟙 _)
    (𝟙 _ ≫ mackeyTranslateMor φ V A p) g' (fun _ => rfl) n y
  rw [s1, s2, cohomologyRes_eq, s3, s4]

variable [(V : Subgroup G).Normal]

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem index_mackeySubgroup_dvd {H : Type u} [Group H] (ψ : H →* G) (x : G) :
    (mackeySubgroup (V : Subgroup G) ψ x).index ∣ (V : Subgroup G).index := by
  rw [mackeySubgroup, Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem mem_shaSubmodule_iff_cohomologyRes (hA : Function.Bijective fun a : A => (V : Subgroup G).index • a)
    (n : ℕ) (y : cohomology A n) :
    y ∈ shaSubmodule φ A n ↔
      (cohomologyRes A (V : Subgroup G) n).hom y ∈
        shaSubmodule (mackeyFamily V φ) (Rep.res (V : Subgroup G).subtype A) n := by
  constructor
  · intro hy p
    rw [cohomologyMapAlong_mackeyFamily_cohomologyRes, hy p.1, map_zero, map_zero]
  · intro hy v
    let p : MackeyIndex V φ := ⟨v, DoubleCoset.mk (V : Subgroup G) (φ v).toMonoidHom.range 1⟩
    have h0 := hy p
    rw [cohomologyMapAlong_mackeyFamily_cohomologyRes] at h0
    have h1 := cohomologyMap_mackeyTranslateMor_injective φ V A p n (h0.trans (map_zero _).symm)
    have hB : Function.Bijective fun a : Rep.res (φ p.1).toMonoidHom A =>
        ((mackeyOpenSubgroup V (continuous_toMonoidHom (φ p.1)) p.2.out : OpenSubgroup (Hv p.1)) :
          Subgroup (Hv p.1)).index • a :=
      bijective_nsmul_of_dvd (index_mackeySubgroup_dvd V (φ p.1).toMonoidHom p.2.out) hA
    exact cohomologyRes_injective_of_bijective (mackeyOpenSubgroup V (continuous_toMonoidHom (φ p.1)) p.2.out)
      (Rep.res (φ p.1).toMonoidHom A) hB n (h1.trans (map_zero _).symm)

end Descent

end

end GroundTheory.ProfCoh
