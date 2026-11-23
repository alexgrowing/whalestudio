import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechPts

open CategoryTheory.Limits

variable {Y X : Scheme.{0}} (f : Y ⟶ X)

def baseOf {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) : U ⟶ X :=
  (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)).app (op U) z

def compOf {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) : U ⟶ Y :=
  (WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i).app (op U) z

theorem compOf_comp {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    compOf f z i ≫ f = baseOf f z := by
  have e := WidePullback.π_arrow (fun _ : Fin (k + 1) => yoneda.map f) i
  have := congrArg (fun t => t.app (op U) z) e
  exact this

theorem ext_comp {k : ℕ} {U : Scheme.{0}} (z z' : Sx (cech f) k U)
    (hb : baseOf f z = baseOf f z') (hc : ∀ i, compOf f z i = compOf f z' i) : z = z' := by
  apply yonedaEquiv.symm.injective
  apply WidePullback.hom_ext (fun _ : Fin (k + 1) => yoneda.map f)
  · intro i
    have : yonedaEquiv (yonedaEquiv.symm z ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) =
        yonedaEquiv (yonedaEquiv.symm z' ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) := by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hc i
    exact yonedaEquiv.injective this
  · have : yonedaEquiv (yonedaEquiv.symm z ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) =
        yonedaEquiv (yonedaEquiv.symm z' ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) := by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hb
    exact yonedaEquiv.injective this

theorem baseOf_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    baseOf f (cechPt f k x y h) = x := by
  have e := WidePullback.lift_base (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
    (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])
  exact (congrArg (fun t => t.app (op U) (𝟙 U)) e).trans (Category.id_comp x)

theorem compOf_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x)
    (i : Fin (k + 1)) : compOf f (cechPt f k x y h) i = y i := by
  have e := WidePullback.lift_π (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
    (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i]) i
  exact (congrArg (fun t => t.app (op U) (𝟙 U)) e).trans (Category.id_comp (y i))

theorem baseOf_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) :
    baseOf f (Sx.res g z) = g ≫ baseOf f z :=
  NatTrans.naturality_apply (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) g.op z

theorem compOf_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    compOf f (Sx.res g z) i = g ≫ compOf f z i :=
  NatTrans.naturality_apply (WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) g.op z

theorem baseOf_along {p k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) :
    baseOf f (Sx.along z θ) = baseOf f z := by
  have e := WidePullback.lift_base (arrows := fun _ : Fin (p + 1) => yoneda.map f)
    (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f))
    (fun i => WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) (θ.toOrderHom i)) (by simp)
  exact congrArg (fun t => t.app (op U) z) e

theorem compOf_along {p k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    compOf f (Sx.along z θ) i = compOf f z (θ.toOrderHom i) := by
  have e := WidePullback.lift_π (arrows := fun _ : Fin (p + 1) => yoneda.map f)
    (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f))
    (fun i => WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) (θ.toOrderHom i)) (by simp) i
  exact congrArg (fun t => t.app (op U) z) e

theorem map_aug {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) :
    Sx.map (cechAug f) z = baseOf f z := rfl

theorem cechPt_spec : CrystallineSemistableComparison.E.CechPt := by
  intro Y X f k U
  refine ⟨fun z => ⟨baseOf f z, compOf f z, compOf_comp f z, ?_⟩, ?_, ?_⟩
  · exact ext_comp f _ _ (baseOf_cechPt f _ _ _).symm fun i => (compOf_cechPt f _ _ _ i).symm
  · intro x y h x' y' h' e
    funext i
    rw [← compOf_cechPt f x y h i, e, compOf_cechPt]
  · intro x y h
    refine ⟨?_, ?_, ?_⟩
    · rw [map_aug, baseOf_cechPt]
    · intro V g
      apply ext_comp
      · rw [baseOf_res, baseOf_cechPt, baseOf_cechPt]
      · intro i
        rw [compOf_res, compOf_cechPt, compOf_cechPt]
    · intro p θ
      apply ext_comp
      · rw [baseOf_along, baseOf_cechPt, baseOf_cechPt]
      · intro i
        rw [compOf_along, compOf_cechPt, compOf_cechPt]

end GlobalTheory.CompanionTheory.CechPts
