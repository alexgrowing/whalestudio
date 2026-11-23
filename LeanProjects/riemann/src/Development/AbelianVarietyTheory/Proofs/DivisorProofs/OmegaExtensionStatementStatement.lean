import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.OmegaHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.OmegaExtensionStatement : GlobalTheory.OmegaHT.ExtSt := by
  first | exact @GlobalTheory.OmegaHT.extSt | exact GlobalTheory.OmegaHT.extSt | (intros; apply GlobalTheory.OmegaHT.extSt <;> assumption)
