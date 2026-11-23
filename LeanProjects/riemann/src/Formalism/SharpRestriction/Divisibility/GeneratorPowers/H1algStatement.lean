import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}

def nuWWOf {L : SizeData₂ D} {P : ParameterChoice' D L} (T : Top D) (Tp : ParamsT D L P) (hK : DV.KapDef D) (j : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : ℝ :=
  letI := T.Q.H.starRing
  (nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn).toReal / (ramOverZ la : ℝ)

def H1algStatement : Prop :=
  ∀ (L : SizeData₂ D) (P : ParameterChoice' D L) (Tp : ParamsT D L P) (hK : DV.KapDef D) (T : Top D) (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (j : ℕ) (hj : InR D j),
    j < D.R.m →
    (letI := T.Q.H.starRing; IntChartEx (T.Q.Xo j) T.Q.c) →
    (letI := T.Q.H.starRing; ChartSaturated (T.Q.Xo j) T.Q.c) →
    (∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) →
    (∃ τ : D.host.E →+* ℂ, InPsi T.Q.H τ ∧
      ∀ x : 𝓞 D.host.E, ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F) = embK T.Q.c τ x) →
    WeightAlgebra.H3 L H C2 A2 CR 0 (lR Tp hK j) Tp.TO →
    (|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) /
        (2 * Module.finrank ℚ D.host.E) ≤ WeightFamilies.RRv D CR →
    (2 * D.R.f * D.R.m : ℝ) ^ 4 * Tp.nWn + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D L C2 A2 →
    D.R.f * D.R.r * (D.R.r + 1) ≤ Tp.nWn →
    (∀ i, (WeightAlgebra.DF (lR Tp hK j) : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < (D.host.g i : ℝ)) →
    ∀ la (y : (recPJ h j hj).Pt la),
      (recPJ h j hj).depth (runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).S.sW (lR Tp hK j) la y ≤
        (((runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).nus la +
          WeightAlgebra.cc D L C2 A2 CR (lR Tp hK j) * (recPJ h j hj).phiC la y : ℝ) : EReal)

end Formalism.MainNotions.ModuliIntegralCharts.H1
