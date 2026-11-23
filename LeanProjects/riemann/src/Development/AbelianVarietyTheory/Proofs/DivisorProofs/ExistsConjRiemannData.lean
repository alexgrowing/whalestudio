import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open GlobalTheory.ArchMetricCompare (cj cjPt_comp val_cj)
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem sqMap_comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} (w : φ ≫ A.hom = A'.hom ≫ f)
    (w' : ψ ≫ A'.hom = A''.hom ≫ g) (w'' : (ψ ≫ φ) ≫ A.hom = A''.hom ≫ g ≫ f) :
    sqMap w'' = sqMap w' ≫ sqMap w :=
  (pullback.map_comp ψ φ ψ φ g f w'.symm w'.symm w.symm w.symm).symm

namespace PPAS.RiemannData

variable {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

def conj : P.RiemannData (spMap (starRingEnd ℂ) ≫ y) :=
  have h := isGrpPullback_pullback d.B cj
  have hL := pull_isLB d.isLB (pullback.fst d.B.hom cj)
  { B := (Over.pullback cj).obj d.B
    φ := pullback.fst d.B.hom cj ≫ d.φ
    isPull := h.comp d.isPull
    L := d.L.pull (pullback.fst d.B.hom cj)
    isLB := hL
    pol := by
      rw [sqMap_comp d.isPull.1.w h.1.w, CechPic.pull_comp, d.pol]
      exact (pull_sqMap_lam h _).trans
        (congrArg (CechPic.lam · _ _) (CechPic.cls_pull d.isLB _ hL).symm)
    u := ConjUnif.conjPull h d.u
    H := d.H.map star
    χ := _
    isAH := ConjUnif.conjPull_isAH h d.u d.isAH }

theorem conj_H : d.conj.H = d.H.map star := rfl

theorem conj_fn (W : P.A.left.Opens) (f : Γ(P.A.left, W)) (z : Fin P.g → ℂ) :
    d.conj.fn W f z = star (d.fn W f (star z)) := by
  have e : (d.conj.u.ex z).left ≫ d.conj.φ = cj ≫ (show Sp ℂ ⟶ _ from (d.u.ex (star z)).left) ≫ d.φ :=
    ArchMetricCompare.cjPt_comp' (isGrpPullback_pullback d.B cj) _
  unfold fn
  rw [← Points.valAt'_eq_valR, ← Points.valAt'_eq_valR]
  exact (congrArg (valAt' · W f) e).trans (val_cj _ _ _)

theorem conj_cov (W : P.A.left.Opens) (f : Γ(P.A.left, W)) (h : ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W) :
    d.conj.cov W f = star (d.cov W f) := by
  have D := (d.differentiableAt_fn f h).hasFDerivAt.star_star
  rw [star_zero] at D
  have e : d.conj.fn W f = star ∘ d.fn W f ∘ star := funext (d.conj_fn W f)
  funext a
  unfold cov
  rw [e, D.fderiv]
  simp

end PPAS.RiemannData

theorem PPAS.exists_conj_riemannData : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ∃ d' : P.RiemannData (spMap (starRingEnd ℂ) ≫ y), d'.H = d.H.map star ∧ ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d'.cov W f = star (d.cov W f) :=
  fun _ _ _ d => ⟨d.conj, d.conj_H, d.conj_cov⟩

end GlobalTheory
