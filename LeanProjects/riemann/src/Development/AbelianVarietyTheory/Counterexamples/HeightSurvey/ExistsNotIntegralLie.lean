import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointFieldFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralLatticeStructureUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ThetaFrameAllOfThetaFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTanAtOfGenericFibre

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.NonIntegralFrameExample

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ThetaFrameCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem spread_holds : SpreadSt Xo c :=
  GlobalTheory.Frames.framedPoint_field_fromTest GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c

theorem all_hold : IntFramesSt Xo c ∧ LieFreeSt Xo c ∧ SpreadSt Xo c :=
  ⟨intFrames Xo c Out.CubePf.cubePull (lieFree Xo c) (thetaFrame_of Xo c GlobalTheory.abelianSchemeLaws_all.2.secTwist)
    (spread_holds Xo c), lieFree Xo c, spread_holds Xo c⟩

variable {Xo c}

def rescale {S : Type} [Field S] [Algebra c.F S] (y : FrPt Xo c S) (a : Sˣ) : FrPt Xo c S :=
  { y with s := scalSec y.x (a : S) y.s, gen := isGenAt_scalSec y.gen a }

theorem exists_framed {S : Type} [Field S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    ∃ y : FrPt Xo c S, y.x = x := by
  choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
  obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist x
  exact ⟨⟨x, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩

end GlobalTheory.NonIntegralFrameExample
