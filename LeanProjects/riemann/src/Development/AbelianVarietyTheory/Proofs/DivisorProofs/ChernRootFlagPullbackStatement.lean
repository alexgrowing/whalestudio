import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernRootFlagPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_root_flag_pullback : ∀ (X Y : AlgebraicGeometry.Scheme.{0}) (f : Y ⟶ X) (E : X.Modules) (N : ℕ) (fl : GlobalTheory.Vert.Flag E N) (i : Fin N), GlobalTheory.Vert.c1 _ ((GlobalTheory.FlagPairExists.flagPull f fl).isLB_root i) = GlobalTheory.Vert.picSymPull f (GlobalTheory.Vert.c1 _ (fl.isLB_root i)) := by
  first | exact @GlobalTheory.FlagPullRoot.c1_root_flagPull | exact GlobalTheory.FlagPullRoot.c1_root_flagPull | (intros; apply GlobalTheory.FlagPullRoot.c1_root_flagPull <;> assumption)
