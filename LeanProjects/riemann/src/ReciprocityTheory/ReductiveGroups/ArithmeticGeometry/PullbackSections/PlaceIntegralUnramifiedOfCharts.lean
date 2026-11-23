import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def ChartValueUnramified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
      IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI → 0 ≤ nval Tc.V e (evI yI f)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
