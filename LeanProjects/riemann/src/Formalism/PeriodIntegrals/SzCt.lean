import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.ElevenLe

noncomputable section

namespace PI.SzCt

open Formalism.BasicNotions Formalism.MainNotions.G

def Uni (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : Prop :=
  L.sc.eps = eps ∧ L.Ct = Ct ∧ L.CGam = CGam ∧ L.Cc = Cc ∧ D.host.CT2 = CT2 ∧
    [P.CkLow, P.Ck6, P.CfL, P.cLL, P.CnW, P.Crho, P.CDelG, P.CLw,
      P.Cj0, P.Cw, P.cw, P.CDel, P.CCount, P.Ch0r, P.Ch0k, P.Ch0N,
      P.Cgap, P.CetaF, P.CY, P.CYL, P.Cpde, P.CccK, P.CF] = PK

def SzCt : Prop :=
  ∀ (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ), ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L),
    Uni eps Ct CGam Cc CT2 PK D L P → x0 ≤ L.sc.x → Formalism.MainNotions.SizesAt L →
    ∀ j ∈ SizeData₂.lifts D, ∀ u : D.what₂.Word,
      ∑ t : HH D, ctD D u j t ≤ 2 * (D.host.TT.card : ℝ) * L.sc.b + 2 * (D.R.f : ℝ) * D.R.k * L.sc.b'

end PI.SzCt
