import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwistChoice

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev thTw (D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) : TwNew D :=
  ⟨D.ntw, D.nexp, D.nStage_trivialCharacter_coeff_eq, th, D.ntwbr, D.ntwbr_ind⟩

theorem carried_thTw (D0 D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) (h : Carried D0 D) :
    Carried D0 (thTw D th).toD7 :=
  ⟨⟨{ h.exp.gal with }, { h.exp.set with }, { h.exp.frm with }, h.exp.br, h.exp.av⟩, h.emb⟩

end GlobalTheory.HeightCounting.Up

end
