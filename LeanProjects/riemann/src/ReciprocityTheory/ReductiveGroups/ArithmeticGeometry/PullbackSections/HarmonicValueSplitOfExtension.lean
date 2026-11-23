import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HarmonicValueOfFiniteExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValFinExtSplit
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

def HarmonicValueAfterExtension : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ) (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)),
        OverLa la T'.V (iT.comp io) e' ∧ yI'.IsAlg ∧
        letI := (iT.comp io).toAlgebra
        ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' (iT.comp io) yI')
          (F : Fin w.n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yI'.1.x)))
          (g : Fin w.n → Germ.PS T'.Fr 1 (chD C.ch)),
          (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yI'.1.s (levPt (T.Q.Xo j) yI'.1.x (x b)) (F b)) ∧
          (∀ b, IsGerm yI'.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (T.Q.l.M ^ 2)
            (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (g b)) ∧
          (∀ b, IsIntPS T' (g b)) ∧
          iT (evI yI f) = (iT.comp io) (((T.Q.l.M : T.Q.c.F) ^ P.totalDegree)⁻¹) *
            ∑ mo ∈ (P.map (iT.comp io)).support, (P.map (iT.comp io)).coeff mo *
              ∏ b, C.ch.B.nabVal T'.Fr C.ch.h T.Q.H.w0 (T.Q.l.M ^ 2) (g b) C.ch.uvec
                (MvPolynomial.monomial (colOf mo b) 1)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
