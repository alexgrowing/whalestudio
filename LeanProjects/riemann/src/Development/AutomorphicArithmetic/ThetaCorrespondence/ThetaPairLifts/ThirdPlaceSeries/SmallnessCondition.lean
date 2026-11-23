import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ExpFrame
open Formalism.CohomologicalDescent.DepthNonnegative
section Tests
variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O)
local instance  : Ring (alg O N lam) := Subalgebra.toRing _
end Tests
end GlobalTheory.ExpFrame
end
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
open GlobalTheory.ExpFrame
namespace GlobalTheory.ExpTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
def InRangeAlt (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i) (_ : Fin (Fm.D x i).R.m) (_ : Par)
    (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → Q Fm x hx i p j P W w
def FrameStatement' : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => FrameAt p j P W w
def GaloisStatement : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => GalAt p j P W w
def SmallnessCondition : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w
end GlobalTheory.ExpTie
end
end
