import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_along_dvr_arcs : ∀ (X : Scheme.{0}) (BD : GlobalTheory.EffCartierData X) (R : Type) [CommRing R] [IsDomain R] (u : R), u ≠ 0 →
    ∀ (x : Sp (FractionRing R) ⟶ X) (n : ℕ),
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X, spMap gam ≫ x = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ u ^ n}) →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.dual BD.lb).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.dual BD.lb) x e := by
  first | exact @GlobalTheory.TraitGen.exists_dual_gen_extAt | exact GlobalTheory.TraitGen.exists_dual_gen_extAt | (intros; apply GlobalTheory.TraitGen.exists_dual_gen_extAt <;> assumption)
