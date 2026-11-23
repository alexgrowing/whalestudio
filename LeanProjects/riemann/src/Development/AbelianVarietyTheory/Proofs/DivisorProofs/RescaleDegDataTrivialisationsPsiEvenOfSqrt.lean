import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem rescale_psiEven : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h eta : D.X → (FractionRing R)ˣ),
    EvenDefect D h → (∀ a b, eta (a + b) = eta a * eta b) → (∀ a, eta a ^ 2 = h a) → (rescale D eta).PsiEven := by
  intro R _ _ D h eta hD hadd hsq
  have h0 : eta 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_eq_left.1 e.symm
  have key : ∀ χ : D.X, eta (-χ) * h χ = eta χ := fun χ => by
    rw [← hsq, pow_two, ← _root_.mul_assoc, ← hadd, neg_add_cancel, h0, _root_.one_mul]
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul _ a b
  refine fun (χ : D.X) => corr_of_val D.P.isLB fun y J hJ => ?_
  show val (LB.mulGen D.P.L _ _ _ _ (GlobalTheory.UU.scaleGen (unitOn (eta (-χ))) (D.psi (-χ)))
      (LB.pullGen D.P.L _ _ D.sym (D.xK χ))) (𝟙 _) y J = val (GlobalTheory.UU.scaleGen (unitOn (eta χ)) (D.psi χ)) (𝟙 _) y J
  refine (val_mul hJ _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen _ _ _ hJ)
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val D.sym r y J) (Category.id_comp _)))).trans ?_
  refine (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) (hD χ y J hJ)).trans ?_)
  refine (_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) ((map_mul _ _ _).symm.trans
    (congrArg (gm _ y ⊤) ((hu _ _).symm.trans (congrArg unitOn (key χ)))))).trans (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm)

end GlobalTheory.PolDeg
