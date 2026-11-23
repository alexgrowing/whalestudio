import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.InducedDropOut
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeMap
import GroundTheory.ProfiniteCohomology.MackeyFormula
import GroundTheory.ProfiniteCohomology.MackeyFormula.CompactSupport
import GroundTheory.ProfiniteCohomology.PoincarePairs.IsDiscreteRepResHomCoindRes
import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section TrivialGroup

variable {k K : Type u} [CommRing k] [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [Subsingleton K]

noncomputable def subsingletonCoindIso (M : Rep.{u} k K) : M ≅ discreteCoind k K M where
  hom := Rep.ofHom ⟨{ toFun := fun m => LocallyConstant.const K m
                      map_add' := fun _ _ => rfl
                      map_smul' := fun _ _ => rfl }, fun g =>
    LinearMap.ext fun m => LocallyConstant.ext fun x => by
      change M.ρ g m = m
      rw [Subsingleton.elim g 1, map_one]
      rfl⟩
  inv := Rep.ofHom ⟨{ toFun := fun f => f 1
                      map_add' := fun _ _ => rfl
                      map_smul' := fun _ _ => rfl }, fun g =>
    LinearMap.ext fun f => by
      change f (1 * g) = M.ρ g (f 1)
      rw [Subsingleton.elim g 1, map_one, mul_one]
      rfl⟩
  hom_inv_id := Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  inv_hom_id := Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f =>
    LocallyConstant.ext fun x => by
      change f 1 = f x
      rw [Subsingleton.elim x 1]))

theorem isZero_cohomology_succ_of_subsingleton (M : Rep.{u} k K) [IsDiscreteRep M] (n : ℕ) :
    IsZero (cohomology M (n + 1)) :=
  (isZero_cohomology_discreteCoind k K M n).of_iso
    { hom := cohomologyMap (subsingletonCoindIso M).hom (n + 1)
      inv := cohomologyMap (subsingletonCoindIso M).inv (n + 1)
      hom_inv_id := by rw [← cohomologyMap_comp, Iso.hom_inv_id, cohomologyMap_id]
      inv_hom_id := by rw [← cohomologyMap_comp, Iso.inv_hom_id, cohomologyMap_id] }

end TrivialGroup

section FreeAction

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (U : Subgroup G) (ι : H →* G)

def InOutCoset (y : G) : Prop :=
  ∃ u : U, y = (u : G) * (DoubleCoset.mk U ι.range y).out

theorem doubleCosetMk_mul_left (u : U) (y : G) :
    DoubleCoset.mk U ι.range ((u : G) * y) = DoubleCoset.mk U ι.range y := by
  simpa using doubleCosetMk_mul_mul U ι y u 1

theorem inOutCoset_mul_left_iff (u : U) (y : G) : InOutCoset U ι ((u : G) * y) ↔ InOutCoset U ι y := by
  unfold InOutCoset
  rw [doubleCosetMk_mul_left]
  constructor
  · rintro ⟨u', hu'⟩
    refine ⟨u⁻¹ * u', ?_⟩
    calc y = (u : G)⁻¹ * ((u : G) * y) := by group
      _ = (u : G)⁻¹ * ((u' : G) * (DoubleCoset.mk U ι.range y).out) := by rw [hu']
      _ = ((u⁻¹ * u' : U) : G) * (DoubleCoset.mk U ι.range y).out := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rintro ⟨u', hu'⟩
    refine ⟨u * u', ?_⟩
    nth_rewrite 1 [hu']
    rw [Subgroup.coe_mul, mul_assoc]

variable [Fintype H] (N : Rep.{u} k U)

theorem exists_norm_eq_res_coind (hfree : ∀ (x : G) (h : H), x * ι h * x⁻¹ ∈ U → h = 1)
    (f : Rep.res ι (Rep.coind U.subtype N))
    (hf : f ∈ (Rep.res ι (Rep.coind U.subtype N)).ρ.invariants) :
    ∃ m, (Rep.res ι (Rep.coind U.subtype N)).ρ.norm m = f := by
  classical
  have hmem : (fun y => if InOutCoset U ι y then f.1 y else 0) ∈
      Representation.coindV U.subtype N.ρ := by
    intro u y
    change (if InOutCoset U ι ((u : G) * y) then f.1 ((u : G) * y) else 0) =
      N.ρ u (if InOutCoset U ι y then f.1 y else 0)
    by_cases hy : InOutCoset U ι y
    · rw [if_pos ((inOutCoset_mul_left_iff U ι u y).2 hy), if_pos hy]
      exact f.2 u y
    · rw [if_neg (mt (inOutCoset_mul_left_iff U ι u y).1 hy), if_neg hy, map_zero]
  refine ⟨⟨_, hmem⟩, Subtype.ext (funext fun y => ?_)⟩
  have hnorm : ((Rep.res ι (Rep.coind U.subtype N)).ρ.norm ⟨_, hmem⟩).1 y =
      ∑ h : H, (if InOutCoset U ι (y * ι h) then f.1 (y * ι h) else 0) := by
    rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hnorm]
  obtain ⟨u₀, h₀, e₀⟩ := exists_eq_mul_out_mul U ι y
  set x := (DoubleCoset.mk U ι.range y).out with hx
  have hD : ∀ h : H, DoubleCoset.mk U ι.range (y * ι h) = DoubleCoset.mk U ι.range y := fun h => by
    have := doubleCosetMk_mul_mul U ι y 1 h
    simpa using this
  have hinv : ∀ h : H, f.1 (y * ι h) = f.1 y := fun h =>
    congrArg (fun g : Rep.res ι (Rep.coind U.subtype N) => g.1 y) (hf h)
  rw [Finset.sum_eq_single h₀⁻¹]
  · rw [if_pos, hinv]
    refine ⟨u₀, ?_⟩
    rw [hD, ← hx, e₀, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  · intro h _ hne
    rw [if_neg]
    rintro ⟨u, hu⟩
    rw [hD, ← hx] at hu
    apply hne
    have key : x * ι (h₀ * h) * x⁻¹ = ((u₀⁻¹ * u : U) : G) := by
      calc x * ι (h₀ * h) * x⁻¹ = (u₀ : G)⁻¹ * ((u₀ : G) * x * ι h₀ * ι h) * x⁻¹ := by
            rw [map_mul]; group
        _ = (u₀ : G)⁻¹ * (y * ι h) * x⁻¹ := by rw [← e₀]
        _ = (u₀ : G)⁻¹ * ((u : G) * x) * x⁻¹ := by rw [hu]
        _ = ((u₀⁻¹ * u : U) : G) := by rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
    exact eq_inv_of_mul_eq_one_right (hfree x _ (key ▸ (u₀⁻¹ * u).2))
  · intro h
    exact absurd (Finset.mem_univ _) h

end FreeAction

section Naturality

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
  {Aᵥ Bᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Bᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v}
  {Aᵣ Bᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Bᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {br : ∀ w, Rep.res (ψ w).toMonoidHom B ⟶ Bᵣ w}
  (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v) (gᵣ : ∀ w, Aᵣ w ⟶ Bᵣ w)
  (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ b v)
  (hgr : ∀ w, ar w ≫ gᵣ w = (Rep.resFunctor (ψ w).toMonoidHom).map g ≫ br w)

end Naturality

section LocalClasses

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

end LocalClasses

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] [∀ v, CompactSpace (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

def FreeOnCosets (U : Subgroup G) : Prop :=
  ∀ w (x : G) (h : F w), x * ψ w h * x⁻¹ ∈ U → h = 1

variable (U : OpenSubgroup G) (N : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep N]

theorem isZero_cohomology_res_coind (hU : FreeOnCosets ψ (U : Subgroup G)) (w : κ) (n : ℕ) :
    IsZero (cohomology (Rep.res (ψ w).toMonoidHom (Rep.coind (U : Subgroup G).subtype N)) (n + 1)) := by
  have hb := mackeyCohomology_bijective U (ψ w) N (n + 1)
  have hsub : ∀ d : MackeyDoubleCoset (U : Subgroup G) (ψ w).toMonoidHom,
      Subsingleton (cohomology (mackeyRep (U : Subgroup G) (ψ w).toMonoidHom N d.out) (n + 1)) :=
    fun d => by
      have : Subsingleton (mackeySubgroup (U : Subgroup G) (ψ w).toMonoidHom d.out) :=
        ⟨fun a b => Subtype.ext ((hU w d.out a ((mem_mackeySubgroup _ _ _ _).1 a.2)).trans
          (hU w d.out b ((mem_mackeySubgroup _ _ _ _).1 b.2)).symm)⟩
      exact ModuleCat.isZero_iff_subsingleton.1 (isZero_cohomology_succ_of_subsingleton _ n)
  have : Subsingleton (cohomology (Rep.res (ψ w).toMonoidHom
      (Rep.coind (U : Subgroup G).subtype N)) (n + 1)) :=
    ⟨fun c c' => hb.1 (funext fun d => Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_of_subsingleton _

omit [IsTopologicalGroup G] [CompactSpace G] [∀ w, IsTopologicalGroup (F w)] [IsDiscreteRep N] in

theorem exists_norm_eq_res_coind' (hU : FreeOnCosets ψ (U : Subgroup G)) (w : κ)
    (f : Rep.res (ψ w).toMonoidHom (Rep.coind (U : Subgroup G).subtype N))
    (hf : f ∈ (Rep.res (ψ w).toMonoidHom (Rep.coind (U : Subgroup G).subtype N)).ρ.invariants) :
    ∃ m, (Rep.res (ψ w).toMonoidHom (Rep.coind (U : Subgroup G).subtype N)).ρ.norm m = f :=
  exists_norm_eq_res_coind (U : Subgroup G) (ψ w).toMonoidHom N (hU w) f hf

noncomputable def tateCoindIso (hU : FreeOnCosets ψ (U : Subgroup G)) (n : ℕ) :
    tateCompactCohomologyRes φ ψ (Rep.coind (U : Subgroup G).subtype N) (n + 1) ≅
      compactCohomology (mackeyFamily U φ) N (mackeyCoeff U φ N) (fun _ => 𝟙 _) (n + 1) :=
  tateForgetIso φ ψ _ _ _ _ _ (fun w n => isZero_cohomology_res_coind ψ U N hU w n)
      (fun w f hf => exists_norm_eq_res_coind' ψ U N hU w f hf) n ≪≫
    mackeyCompactCohomologyIso U φ N (n + 1)

theorem tateCoindIso_hom (hU : FreeOnCosets ψ (U : Subgroup G)) (n : ℕ) :
    (tateCoindIso φ ψ U N hU n).hom =
      tateForget φ ψ _ _ _ _ _ (n + 1) ≫ (mackeyCompactCohomologyIso U φ N (n + 1)).hom :=
  rfl

noncomputable def tateCompactCores (hU : FreeOnCosets ψ (U : Subgroup G)) (A : Rep.{u} k G)
    [IsDiscreteRep A] (n : ℕ) :
    compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype A) (n + 1) ⟶
      tateCompactCohomologyRes φ ψ A (n + 1) :=
  (tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU n).inv ≫
    tateCompactCohomologyMap φ ψ
      (Aᵥ := fun v => Rep.res (φ v).toMonoidHom
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)))
      (Bᵥ := fun v => Rep.res (φ v).toMonoidHom A)
      (Aᵣ := fun w => Rep.res (ψ w).toMonoidHom
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)))
      (Bᵣ := fun w => Rep.res (ψ w).toMonoidHom A)
      (coindTrace (U : Subgroup G) A)
      (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (coindTrace (U : Subgroup G) A))
      (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (coindTrace (U : Subgroup G) A))
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) (n + 1)

end Tate

end GroundTheory.ProfCoh
