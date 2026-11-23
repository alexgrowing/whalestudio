import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGrpPull

theorem inv_left_comp {S T : Scheme.{0}} (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S)
    (α : B.left ⟶ A.left) (h : IsGrpPullback B A y α) :
    (GrpObj.inv : B ⟶ B).left ≫ α = α ≫ (GrpObj.inv : A ⟶ A).left := by
  have hw : α ≫ A.hom = B.hom ≫ y := h.1.w
  let f : (B ⟶ B) → (Over.mk (B.hom ≫ y) ⟶ A) := fun x =>
    Over.homMk (x.left ≫ α) (by
      change (x.left ≫ α) ≫ A.hom = B.hom ≫ y
      rw [Category.assoc, hw, ← Category.assoc, Over.w x])
  have hmul : ∀ x z : B ⟶ B, f (x * z) = f x * f z := fun x z =>
    Over.OverMorphism.ext (h.2 B x z (f x) (f z) rfl rfl).symm
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [← hmul, _root_.mul_one, _root_.mul_one]
    exact mul_left_cancel e
  have hinv : f (𝟙 B)⁻¹ = (f (𝟙 B))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, _root_.inv_mul_cancel, h1]
  have e := congrArg CommaMorphism.left hinv
  have e' : ((𝟙 B ≫ GrpObj.inv : B ⟶ B)).left ≫ α = (f (𝟙 B) ≫ GrpObj.inv).left := e
  simpa [f] using e'

theorem symm_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  intro S T A _ B _ y α h L hL hs
  have e := inv_left_comp A B y α h
  have h1 := GenSpread.lbIso_pull_pull hL (a := α) (GrpObj.inv : B ⟶ B).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : A ⟶ A).left) α e
  have h3 := GenSpread.lbIso_pullback hs α
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h1)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h2 h3)

end GlobalTheory.SymGrpPull
