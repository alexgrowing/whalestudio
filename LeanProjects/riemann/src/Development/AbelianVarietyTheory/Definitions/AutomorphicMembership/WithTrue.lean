import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ResCharThetaJetPlaceDegOne
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.Mem

def GJStage.withTrue {B : Base} {C : Cols B} (G : GJStage B C) : GJStage B C :=
  letI := B.host.cmStar
  { G with
    vol := fun W => Vol.trueVol B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    vol_pos := fun W => Vol.trueVol_pos B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    gx := Per.trueGx B.host B.embLL B.embE (Equiv.refl _) }

def Base.dsigTrue (B : Base) (τ : Tau B.R) : ℝ := Vol.trueDsig B.R (B.hc τ)

end GlobalTheory.Mem
