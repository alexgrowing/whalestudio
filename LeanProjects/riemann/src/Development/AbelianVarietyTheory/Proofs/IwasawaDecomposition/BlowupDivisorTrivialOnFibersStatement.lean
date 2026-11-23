import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorTrivialOnFibers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blowup_divisor_trivial_on_fibers : ∀ {S S' X' : Scheme.{0}} (B : GlobalTheory.EffCartierData S') (n : ℕ) (h : S ⟶ S') (q : S ⟶ X')
    (I : X'.IdealSheafData), IsIso h → FinalTheorems.EffCartier I → I.comap q = (B.idealSheaf ^ n).comap h →
    ∀ (W : Scheme.{0}) (K : Type) [Field K] (g : W ⟶ S) (a : W ⟶ Sp K) (x0 : Sp K ⟶ X'), g ≫ q = a ≫ x0 →
    GlobalTheory.CechPic.pull (g ≫ h) (n • GlobalTheory.CechPic.cls B.lb B.isLB_lb) = 0 := by
  first | exact @GlobalTheory.pull_nsmul_cls_eq_zero_of_comap | exact GlobalTheory.pull_nsmul_cls_eq_zero_of_comap | (intros; apply GlobalTheory.pull_nsmul_cls_eq_zero_of_comap <;> assumption)
