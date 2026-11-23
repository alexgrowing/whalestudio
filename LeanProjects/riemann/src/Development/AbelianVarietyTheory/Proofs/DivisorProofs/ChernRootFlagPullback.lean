import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagPullRoot

theorem c1_root_flagPull : ∀ (X Y : AlgebraicGeometry.Scheme.{0}) (f : Y ⟶ X) (E : X.Modules) (N : ℕ) (fl : GlobalTheory.Vert.Flag E N) (i : Fin N), GlobalTheory.Vert.c1 _ ((GlobalTheory.FlagPairExists.flagPull f fl).isLB_root i) = GlobalTheory.Vert.picSymPull f (GlobalTheory.Vert.c1 _ (fl.isLB_root i)) := by
  intro X Y f E N fl i
  have h₁ := pull_isLB (fl.isLB_root i) f
  rw [GlobalTheory.Vert.pullback_firstChern f (fl.isLB_root i) h₁]
  refine GlobalTheory.Vert.firstChernCongr _ _ ?_
  have e : LBIso ((fl.root i).pull f) (GlobalTheory.VB.det ((fl.pull f).gr i) 1) :=
    ((fl.isVB_gr i).lbIso_det_pullback f).trans h₁ ((fl.isVB_gr i).pullback f).isLB_det
      ((fl.pull f).isLB_root i) (((fl.isVB_gr i).pullback f).lbIso_det_of_iso (fl.pullGrIso f i))
  exact e.symm

end GlobalTheory.FlagPullRoot
