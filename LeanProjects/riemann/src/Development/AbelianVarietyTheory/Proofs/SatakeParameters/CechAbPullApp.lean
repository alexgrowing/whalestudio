import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FlatHermRootLineDegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe v v' u u'

noncomputable section

namespace GlobalTheory

structure Cube.PullHom {ι κ : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
    (σ : R →+* S) (τ : κ → ι) (A : Cube.{v} ι R) (B : Cube.{v'} κ S) where

  app : ∀ s : Finset κ, A.obj (s.image τ) →ₛₗ[σ] B.obj s

  app_res : ∀ {s t : Finset κ} (h : s ⊆ t) (x : A.obj (s.image τ)),
    app t (Cube.res A (Finset.image_subset_image h) x) = Cube.res B h (app s x)

namespace Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R] {S : Type u'} [Ring S]
  {σ : R →+* S} {τ : κ → ι} {A : Cube.{v} ι R} {B : Cube.{v'} κ S} (ψ : Cube.PullHom σ τ A B)

theorem card_image {p : ℕ} (t : {s : Finset κ // s.card = p}) (h : Set.InjOn τ (t.1 : Set κ)) :
    (t.1.image τ).card = p := by
  rw [Finset.card_image_of_injOn h, t.2]

open Classical in

def term (p : ℕ) : Cube.Term A p →ₛₗ[σ] Cube.Term B p where
  toFun x t := if h : Set.InjOn τ (t.1 : Set κ) then
      PD.sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, card_image t h⟩) else 0
  map_add' x y := by
    funext t
    by_cases h : Set.InjOn τ (t.1 : Set κ)
    · simp only [dif_pos h, Pi.add_apply, map_add, smul_add]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' r x := by
    funext t
    by_cases h : Set.InjOn τ (t.1 : Set κ)
    · simp only [dif_pos h, Pi.smul_apply, map_smulₛₗ, smul_comm (PD.sortSign τ t.1) (σ r)]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero]

theorem term_apply_of_injOn {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : Set.InjOn τ (t.1 : Set κ)) :
    ψ.term p x t = PD.sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, card_image t h⟩) := by
  unfold term
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]

theorem term_apply_of_not_injOn {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : ¬ Set.InjOn τ (t.1 : Set κ)) : ψ.term p x t = 0 := by
  unfold term
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg h]

end Cube.PullHom

section Sheaf

open SheafPull

variable {T T' : TopCat.{u}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {V : Opens T}
  {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'} (τ : κ → ι)
  (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
  {F : AbSheaf T} {G : AbSheaf T'}

def cechAbPull (φ : F ⟶ (push f).obj G) :
    Cube.PullHom (RingHom.id ℤ) τ (cechAbCube F.obj V U) (cechAbCube G.obj V' U') where
  app s := (G.obj.map (homOfLE (hτ s)).op).hom.toIntLinearMap ∘ₗ
    (φ.hom.app (op (cechOpen V U (s.image τ)))).hom.toIntLinearMap
  app_res {s t} h x := by
    have e : φ.hom.app (op (cechOpen V U (t.image τ)))
        (F.obj.map (homOfLE (cechOpen_anti V U (Finset.image_subset_image (f := τ) h))).op x) =
        G.obj.map ((Opens.map f).map
          (homOfLE (cechOpen_anti V U (Finset.image_subset_image (f := τ) h)))).op
          (φ.hom.app (op (cechOpen V U (s.image τ))) x) :=
      ConcreteCategory.congr_hom (φ.hom.naturality _) x
    refine (congrArg (G.obj.map (homOfLE (hτ t)).op) e).trans ?_
    refine (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp (homOfLE (hτ s)).op
        (homOfLE (cechOpen_anti V' U' h)).op) _))
    rfl

theorem cechAbPull_app (φ : F ⟶ (push f).obj G) (s : Finset κ)
    (x : F.obj.obj (op (cechOpen V U (s.image τ)))) :
    (cechAbPull f τ hτ φ).app s x =
      G.obj.map (homOfLE (hτ s)).op (φ.hom.app (op (cechOpen V U (s.image τ))) x) := rfl

end Sheaf

end GlobalTheory
