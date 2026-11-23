import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section General

variable (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

theorem tateCompactCohomology_eq_zero_of_surjective_of_injective (n : ℕ)
    (hs : Function.Surjective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1)).hom)
    (hi : Function.Injective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 2)).hom)
    (x : tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 2)) : x = 0 := by
  have h1 : (tateToGlobal φ ψ A Aᵥ a Aᵣ ar (n + 2)).hom x = 0 := by
    apply hi
    rw [map_zero]
    exact hom_apply_hom_apply_of_comp_eq (tateToGlobal_tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1)) x
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (tateCompactCohomology_exact_compact φ ψ A Aᵥ a Aᵣ ar (n + 1)) x h1
  obtain ⟨y, rfl⟩ := hs z
  rw [← hz]
  exact hom_apply_hom_apply_of_comp_eq (tateGlobalToLocal_tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n) y

theorem injective_tateGlobalToLocal_of_eq_zero (n : ℕ)
    (h : ∀ x : tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1), x = 0) :
    Function.Injective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1)).hom := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (tateCompactCohomology_exact_global φ ψ A Aᵥ a Aᵣ ar n) y hy
  rw [h x]
  exact map_zero _

theorem surjective_tateGlobalToLocal_of_eq_zero (n : ℕ)
    (h : ∀ x : tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 2), x = 0) :
    Function.Surjective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1)).hom := fun z =>
  (ShortComplex.moduleCat_exact_iff _).1 (tateCompactCohomology_exact_local φ ψ A Aᵥ a Aᵣ ar n) z
    (h _)

omit [∀ w, Fintype (F w)] in

theorem injective_tateGlobalToLocal_iff (n : ℕ) (hv : ∀ v, Subsingleton (cohomology (Aᵥ v) n)) :
    Function.Injective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n).hom ↔
      Function.Injective (globalToLocal ψ A Aᵣ ar n).hom := by
  constructor
  · intro h x y hxy
    refine h (Prod.ext (funext fun v => Subsingleton.elim _ _) ?_)
    exact hxy
  · intro h x y hxy
    exact h (congrArg Prod.snd hxy)

omit [∀ w, Fintype (F w)] in

theorem surjective_tateGlobalToLocal_iff (n : ℕ) (hv : ∀ v, Subsingleton (cohomology (Aᵥ v) n)) :
    Function.Surjective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n).hom ↔
      Function.Surjective (globalToLocal ψ A Aᵣ ar n).hom := by
  constructor
  · intro h z
    obtain ⟨x, hx⟩ := h (0, z)
    exact ⟨x, congrArg Prod.snd hx⟩
  · intro h z
    obtain ⟨x, hx⟩ := h z.2
    exact ⟨x, Prod.ext (funext fun v => Subsingleton.elim _ _) hx⟩

end General

section Res

attribute [local instance 2000] Rep.hV2

theorem eq_zero_tateCompactCohomologyRes_of_shortExact {S : ShortComplex (Rep.{u} k G)}
    [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (n : ℕ)
    (h₁ : ∀ x : tateCompactCohomologyRes φ ψ S.X₁ n, x = 0)
    (h₃ : ∀ x : tateCompactCohomologyRes φ ψ S.X₃ n, x = 0)
    (x : tateCompactCohomologyRes φ ψ S.X₂ n) : x = 0 := by
  have : ∀ v, IsDiscreteRep (S.map (Rep.resFunctor (φ v).toMonoidHom)).X₁ := fun v =>
    IsDiscreteRep.res (continuous_toMonoidHom (φ v)) _
  have : ∀ v, IsDiscreteRep (S.map (Rep.resFunctor (φ v).toMonoidHom)).X₂ := fun v =>
    IsDiscreteRep.res (continuous_toMonoidHom (φ v)) _
  have : ∀ v, IsDiscreteRep (S.map (Rep.resFunctor (φ v).toMonoidHom)).X₃ := fun v =>
    IsDiscreteRep.res (continuous_toMonoidHom (φ v)) _
  have : ∀ w, IsDiscreteRep (S.map (Rep.resFunctor (ψ w).toMonoidHom)).X₁ := fun w =>
    IsDiscreteRep.res (continuous_toMonoidHom (ψ w)) _
  have : ∀ w, IsDiscreteRep (S.map (Rep.resFunctor (ψ w).toMonoidHom)).X₂ := fun w =>
    IsDiscreteRep.res (continuous_toMonoidHom (ψ w)) _
  have : ∀ w, IsDiscreteRep (S.map (Rep.resFunctor (ψ w).toMonoidHom)).X₃ := fun w =>
    IsDiscreteRep.res (continuous_toMonoidHom (ψ w)) _
  have hE := tateCompactCohomology_exact₂ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hE x (h₃ _)
  rw [← hy, h₁ y]
  exact map_zero _

theorem tateCompactCohomologyMap_eq_id {A : Rep.{u} k G} [IsDiscreteRep A] {Aᵥ : ∀ v, Rep.{u} k (H v)}
    [∀ v, IsDiscreteRep (Aᵥ v)] {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v}
    {Aᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w}
    (g : A ⟶ A) (gᵥ : ∀ v, Aᵥ v ⟶ Aᵥ v) (gᵣ : ∀ w, Aᵣ w ⟶ Aᵣ w)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ a v)
    (hgr : ∀ w, ar w ≫ gᵣ w = (Rep.resFunctor (ψ w).toMonoidHom).map g ≫ ar w)
    (e : g = 𝟙 A) (eᵥ : ∀ v, gᵥ v = 𝟙 _) (eᵣ : ∀ w, gᵣ w = 𝟙 _) (n : ℕ) :
    tateCompactCohomologyMap φ ψ g gᵥ gᵣ hg hgr n = 𝟙 _ := by
  subst e
  obtain rfl : gᵥ = fun v => 𝟙 (Aᵥ v) := funext eᵥ
  obtain rfl : gᵣ = fun w => 𝟙 (Aᵣ w) := funext eᵣ
  exact tateCompactCohomologyMap_id φ ψ n

theorem eq_zero_tateCompactCohomologyRes_of_retract {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (i : A ⟶ B) (p : B ⟶ A) (hip : i ≫ p = 𝟙 A) (n : ℕ)
    (hB : ∀ x : tateCompactCohomologyRes φ ψ B n, x = 0) (x : tateCompactCohomologyRes φ ψ A n) :
    x = 0 := by
  have hi : ∀ v, 𝟙 (Rep.res (φ v).toMonoidHom A) ≫ (Rep.resFunctor (φ v).toMonoidHom).map i =
      (Rep.resFunctor (φ v).toMonoidHom).map i ≫ 𝟙 _ := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hir : ∀ w, 𝟙 (Rep.res (ψ w).toMonoidHom A) ≫ (Rep.resFunctor (ψ w).toMonoidHom).map i =
      (Rep.resFunctor (ψ w).toMonoidHom).map i ≫ 𝟙 _ := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hp : ∀ v, 𝟙 (Rep.res (φ v).toMonoidHom B) ≫ (Rep.resFunctor (φ v).toMonoidHom).map p =
      (Rep.resFunctor (φ v).toMonoidHom).map p ≫ 𝟙 _ := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hpr : ∀ w, 𝟙 (Rep.res (ψ w).toMonoidHom B) ≫ (Rep.resFunctor (ψ w).toMonoidHom).map p =
      (Rep.resFunctor (ψ w).toMonoidHom).map p ≫ 𝟙 _ := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hcomp := tateCompactCohomologyMap_comp φ ψ i (fun v => (Rep.resFunctor (φ v).toMonoidHom).map i)
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map i) hi hir p
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map p) (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map p)
    hp hpr n
  rw [tateCompactCohomologyMap_eq_id φ ψ _ _ _ _ _ hip
    (fun v => by rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id])
    (fun w => by rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id])] at hcomp
  have hx := congrArg (fun f => f.hom x) hcomp
  change x = _ at hx
  rw [hx]
  change (tateCompactCohomologyMap φ ψ p _ _ hp hpr n).hom
    ((tateCompactCohomologyMap φ ψ i _ _ hi hir n).hom x) = 0
  rw [hB ((tateCompactCohomologyMap φ ψ i _ _ hi hir n).hom x)]
  exact map_zero _

end Res

end Tate

end GroundTheory.ProfCoh
