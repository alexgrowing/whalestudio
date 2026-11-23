import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfLevelSubmodulePermutation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_level_submodule_permutation : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : RowsT p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.actC p i hp.1 (φ h)) v ∈ A (h • y) := by
  first | exact @GlobalTheory.DefSplit.split_lift | exact GlobalTheory.DefSplit.split_lift | (intros; apply GlobalTheory.DefSplit.split_lift <;> assumption)
