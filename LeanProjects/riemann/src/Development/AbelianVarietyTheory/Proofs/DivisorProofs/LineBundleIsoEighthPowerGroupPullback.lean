import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem lift_left_comp {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left}
    {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (hsq : IsSquare χ χ₂)
    (x y : B ⟶ C) (x' y' : B' ⟶ C') (hx : x'.left ≫ χ = φB ≫ x.left) (hy : y'.left ≫ χ = φB ≫ y.left) :
    (lift x' y').left ≫ χ₂ = φB ≫ (lift x y).left := by
  have f1 : (lift x y).left ≫ (fst C C).left = x.left := congrArg (fun q => q.left) (lift_fst x y)
  have f2 : (lift x y).left ≫ (snd C C).left = y.left := congrArg (fun q => q.left) (lift_snd x y)
  have f1' : (lift x' y').left ≫ (fst C' C').left = x'.left := congrArg (fun q => q.left) (lift_fst x' y')
  have f2' : (lift x' y').left ≫ (snd C' C').left = y'.left := congrArg (fun q => q.left) (lift_snd x' y')
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ (fst C C).left = (_ ≫ _) ≫ (fst C C).left
    rw [Category.assoc, hsq.1, ← Category.assoc, f1', hx, Category.assoc, f1]
  · show (_ ≫ _) ≫ (snd C C).left = (_ ≫ _) ≫ (snd C C).left
    rw [Category.assoc, hsq.2, ← Category.assoc, f2', hy, Category.assoc, f2]

theorem lbIso_eighth_pull : ∀ {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (Q : LB (C ⊗ C).left) (Q' : LB (C' ⊗ C').left) (L : LB B.left) (L' : LB B'.left) (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (W : Matrix (Fin 8) (Fin 8) ℤ), Q.IsLB → Q'.IsLB → L.IsLB → L'.IsLB → IsSquare χ χ₂ → LBIso Q' (Q.pull χ₂) → (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) → LBIso L' (L.pull φB) → LBIso L (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → LBIso L' (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  intro T T' B C B' C' φB χ χ₂ Q Q' L L' pr pr' W hQ hQ' hL hL' hsq HQ hpr h1 hLL
  have h3 := GlobalTheory.ShapePull.iso_linComb_pull HQ (K := Fin 8 × Fin 8)
    (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2) φB (fun ab => lift_left_comp hsq _ _ _ _ (hpr ab.1) (hpr ab.2))
  have h2 := GlobalTheory.SiegelPullComp.iso_pull φB hLL
  have lc : (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hQ _ _
  have lc' : (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hQ' _ _
  exact LBIso.trans hL' (pull_isLB hL φB) lc' h1
    (LBIso.trans (pull_isLB hL φB) (pull_isLB lc φB) lc' h2 h3.symm)

end GlobalTheory.Poinc.Eq8
