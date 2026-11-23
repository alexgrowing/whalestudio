import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.ElevenLe

noncomputable section

namespace PI.SzEatI

open Formalism.BasicNotions Formalism.MainNotions.G

def Uni (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : Prop :=
  L.sc.eps = eps ∧ L.Ct = Ct ∧ L.CGam = CGam ∧ L.Cc = Cc ∧ D.host.CT2 = CT2 ∧
    [P.CkLow, P.Ck6, P.CfL, P.cLL, P.CnW, P.Crho, P.CDelG, P.CLw,
      P.Cj0, P.Cw, P.cw, P.CDel, P.CCount, P.Ch0r, P.Ch0k, P.Ch0N,
      P.Cgap, P.CetaF, P.CY, P.CYL, P.Cpde, P.CccK, P.CF] = PK

def SzEatI : Prop :=
  ∀ (K : Consts) (ce : ErrC) (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ,
    ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L),
    Uni eps Ct CGam Cc CT2 PK D L P → x0 ≤ L.sc.x → Formalism.MainNotions.SizesAt L →
    ∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ (IsResidueClassZero D p ∨ IsSg D p) ∧ ¬ (IsResidueClassZero D p ∧ hP D p = 0) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) →
      ∑ p ∈ S, Real.log p * (EatI L K ce j p - max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ))) ≤
        C * (D.R.f : ℝ) * L.sc.b * Real.log (L.sc.X'' D.R.n)

end PI.SzEatI
