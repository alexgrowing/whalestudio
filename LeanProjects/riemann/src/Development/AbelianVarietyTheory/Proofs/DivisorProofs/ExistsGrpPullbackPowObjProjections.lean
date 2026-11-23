import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

theorem exists_powPr_of_isGrpPullback : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u := by
  intro S T t A _ A' _ φ' B' _ r φB hA hB
  have wu : ∀ u : Fin r, (φB ≫ (Out.powPr A u).left) ≫ A.hom = B'.hom ≫ t := fun u => by
    rw [Category.assoc, Over.w (Out.powPr A u)]; exact hB.1.w
  let pr' : Fin r → (B' ⟶ A') := fun u => Over.homMk (hA.1.lift _ _ (wu u)) (hA.1.lift_snd _ _ _)
  have hpr : ∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left := fun u => hA.1.lift_fst _ _ _
  have inj : ∀ {X : Over T} (a b : X ⟶ A'), a.left ≫ φ' = b.left ≫ φ' → a = b := fun a b h =>
    Over.OverMorphism.ext (hA.1.hom_ext h ((Over.w a).trans (Over.w b).symm))
  have key : ∀ {X : Over T} (z : X ⟶ B') (u : Fin r),
      pushPt hA.1.w (z ≫ pr' u) = pushPt hB.1.w z ≫ Out.powPr A u := fun z u =>
    Over.OverMorphism.ext (by
      show (z.left ≫ (pr' u).left) ≫ φ' = (z.left ≫ φB) ≫ (Out.powPr A u).left
      rw [Category.assoc, hpr, Category.assoc])
  refine ⟨pr', fun u => ?_, hpr, fun X y => ?_⟩
  · refine GlobalTheory.Serre.isMonHom_of_mul_comp _ fun X x y => inj _ _ ?_
    have hm : pushPt hB.1.w (x * y) = pushPt hB.1.w x * pushPt hB.1.w y := map_mul (pushHom hB X) x y
    calc ((x * y) ≫ pr' u).left ≫ φ' = (pushPt hA.1.w ((x * y) ≫ pr' u)).left := rfl
      _ = ((pushPt hB.1.w x * pushPt hB.1.w y) ≫ Out.powPr A u).left := by rw [key, hm]
      _ = ((pushPt hB.1.w x ≫ Out.powPr A u) * (pushPt hB.1.w y ≫ Out.powPr A u)).left := by
        rw [MonObj.mul_comp]
      _ = (pushPt hA.1.w (x ≫ pr' u) * pushPt hA.1.w (y ≫ pr' u)).left := by rw [key, key]
      _ = ((x ≫ pr' u) * (y ≫ pr' u)).left ≫ φ' := hA.2 X _ _ _ _ rfl rfl
  · let z : Over.mk (X.hom ≫ t) ⟶ Out.powObj A r :=
      (Out.powIsLimit A r).lift (Fan.mk (Over.mk (X.hom ≫ t)) fun u => pushPt hA.1.w (y u))
    have hz : ∀ u, z ≫ Out.powPr A u = pushPt hA.1.w (y u) := fun u =>
      (Out.powIsLimit A r).fac (Fan.mk (Over.mk (X.hom ≫ t)) fun u => pushPt hA.1.w (y u)) ⟨u⟩
    have hz0 : z.left ≫ (Out.powObj A r).hom = X.hom ≫ t := Over.w z
    let x : X ⟶ B' := Over.homMk (hB.1.lift z.left X.hom hz0) (hB.1.lift_snd _ _ _)
    have comp : ∀ (x₁ : X ⟶ B') (u : Fin r), (x₁ ≫ pr' u).left ≫ φ' = x₁.left ≫ φB ≫ (Out.powPr A u).left :=
      fun x₁ u => by
        show (x₁.left ≫ (pr' u).left) ≫ φ' = _
        rw [Category.assoc, hpr]
    have uniq : ∀ x₁ x₂ : X ⟶ B', (∀ u, x₁ ≫ pr' u = y u) → (∀ u, x₂ ≫ pr' u = y u) → x₁ = x₂ := by
      intro x₁ x₂ h₁ h₂
      refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w x₁).trans (Over.w x₂).symm))
      refine powext A r _ _ ?_ fun k => ?_
      · rw [Category.assoc, Category.assoc, hB.1.w, ← Category.assoc, ← Category.assoc, Over.w x₁, Over.w x₂]
      · rw [Category.assoc, Category.assoc, ← comp x₁ k, ← comp x₂ k, h₁, h₂]
    have hx : ∀ u, x ≫ pr' u = y u := fun u => inj _ _ (by
      rw [comp]
      show hB.1.lift z.left X.hom hz0 ≫ φB ≫ (Out.powPr A u).left = (y u).left ≫ φ'
      rw [← Category.assoc, hB.1.lift_fst]
      exact congrArg (fun w => w.left) (hz u))
    exact ⟨x, hx, fun x₁ h₁ => uniq _ _ h₁ hx⟩

end GlobalTheory.ActFin
