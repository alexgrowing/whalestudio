import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}

open Classical in

def clOf {j : ℕ} (wL : WeightFamilies.Wt D j) {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  if ((D.host.QS : ℕ) : 𝓞 K) ∈ la.asIdeal then (padicValNat (ringChar (𝓞 K ⧸ la.asIdeal)) D.host.QS : ℝ) * (c2 D wL : ℝ)
  else if ((D.host.q : ℕ) : 𝓞 K) ∈ la.asIdeal ∨ ((D.host.d : ℕ) : 𝓞 K) ∈ la.asIdeal then (cHalf wL : ℝ)
  else 0

def RStatement : Prop :=
  ∀ (L : SizeData₂ D) (P : ParameterChoice' D L) (Tp : ParamsT D L P) (hK : DV.KapDef D) (T : Top D) (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (nuWW : ℕ → HeightOneSpectrum (𝓞 T.Q.c.F) → ℝ)
    (j : ℕ) (hj : InR D j) (RR PP qmin : ℝ),
    j < D.R.m →
    (letI := T.Q.H.starRing; IntChartEx (T.Q.Xo j) T.Q.c) →
    (T.Q.l.M : ℕ) = D.host.g 0 * D.host.g 1 →
    D.host.rdE ^ 2 / (4 * D.R.f) ≤ RR →
    ((2 * D.R.f * D.R.m : ℕ) : ℝ) ^ 3 ≤ PP →
    0 < qmin → qmin ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) →
    (WeightAlgebra.DF (lR Tp hK j) : ℝ) * 2 * Real.sqrt ((2 * D.R.f * D.R.m : ℕ) : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) →
    4 * WeightAlgebra.DF (lR Tp hK j) + 4 ≤ D.host.g 0 * D.host.g 1 →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)),
    (∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
    ∀ (y : (recPJ h j hj).Pt la) (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (_ : OverLa la T'.V io e)
      (z : IntFr (T.Q.Xo j) T.Q.c T' io) (_ : z.IsAlg) (eta : T.G.PY j (WeightAlgebra.resCh la)) (_ : T.G.lies j la T' io z eta),
      (show T.PtA j la from y).1 = profI (T.Q.Xo j) T.Q.c (T.G.PY j (WeightAlgebra.resCh la)) e z eta →
      (recPJ h j hj).depth (runOf Tp hK (recB h.toLawsCore) hinj EX nuWW j).S.sW (lR Tp hK j) la y ≤
        (letI := T.Q.H.starRing; nuLoc z e T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn) +
          (((ramOverZ la : ℝ) * clOf (lR Tp hK j) la +
            RR * PP * (WeightAlgebra.DF (lR Tp hK j) : ℝ) ^ 2 / qmin * (recPJ h j hj).phiC la y : ℝ) : EReal)

end Formalism.MainNotions.ModuliIntegralCharts.H1
