import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.DepthPins

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions

variable {D : D7}

structure LawsPi (T : Core D) (Dd : DepData D.host.E) : Prop where

  page : Dd.Q.g1 = D.host.g 0 ∧ Dd.Q.g2 = D.host.g 1 ∧ Dd.Q.q1 = D.host.q ∧ Dd.Q.dd = D.host.d ∧ Dd.Q.f = D.R.f ∧
    Dd.Q.r = D.R.r
  tPos : TPos Dd

  sm : Dd.Q.sm = D.host.small

  wts : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j

  piSplit : PiSplit (H := T.Q.H) Dd
  piHalf : PiHalf T.Q.l Dd

structure LawsDep (T : Core D) [StarRing (𝓞 D.host.E)] : Prop where

  star_eq : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a

  chartEx : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c
  chartIndep : ∀ j, InR D j → ChartIndep (T.Q.Xo j) T.Q.c

def NuFinAt (T : Core D) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)] : Prop :=
  ∀ j, InR D j → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nuWAt (Xo := T.Q.Xo j) Dd la j ≠ ⊤

def nuE (T : Core D) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)] (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    ENNReal :=
  (nuWAt (Xo := T.Q.Xo j) Dd la j).toENNReal

end Formalism.L2.Pj
