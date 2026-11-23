import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRationalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesSupLatticeAndCommutesTypeGroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeCommuteOfTwistSeriesSideDataStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem supLaws_of_sides (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E)
    (h : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) :
    SupG D ∧ SupFull D ∧ SupHk D ∧ CommG D ∧ HkComm D := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.twistedFormSupLattice_full_groupStable_of_eq_rational D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS Y.sup X.integral
  obtain ⟨h3, h4⟩ := GlobalTheory.T.hecke_preserves_supLattice_and_commutes_typeGroup D X E Y h
  exact ⟨h1, h2, h3, h4, GlobalTheory.T.splitPlaceHeckeCommute_of_twistSeriesSideData D X E Y⟩

end GlobalTheory.TwInputs
