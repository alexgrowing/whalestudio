import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Indef.Tree.DepthTie

open NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.DIV Formalism.BasicNotions Formalism.L2.Indef.Tree.DepthCond

section Sat

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
  {Dw : ℕ → Datum H} (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

end Sat

section CoreSat

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (T : Core D) [StarRing (𝓞 D.host.E)] (Dd : DepData D.host.E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

theorem leafDepthRam_core_sat (N : IndefNum Bs) (Nd : NumDatum) (hL : LawsPi T Dd) (hp : T.Q.Pins)
    (hι : ∀ j, InR D (ι j))
    (hE : ∀ v j, O.E v j = EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) Dd v (ι j))
    (hσ : ∀ v j, O.σ v j = sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) Dd (ι j))
    (hT : O.T = ((Dd.Q.T : ℕ) : ℝ))
    (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm)
    (hstar : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) (hEx : ∀ j, IntChartEx (T.Q.Xo (ι j)) T.Q.c)
    (hPg : LeafPage O) (hSz : LeafSizes O) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd) (tK : TieFK O Nd)
    (Dk : Bs.J → ℝ) (C₀ : ℝ) (iD : DegScale O (fun j => (DF (T.Q.Dw (ι j)) (Dd.aL (ι j)) : ℝ)) Dk)
    (iW : DegWeight O Dk C₀) (iP : PageRam O C₀) (iB : WtRam O Nd ι) : LeafDepthRam N O :=
  leafDepthRam_core T Dd O ι N Nd hL hp hι hE hσ hT hpr hstar hEx
    (fun j => Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds (T.Q.Xo (ι j)) T.Q.c) hPg hSz tF tP tK Dk C₀ iD iW iP iB

end CoreSat

section NuFin

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

theorem nuFinAt_of_chartEx {D : D7} (T : Core D) (hp : T.Q.Pins) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)]
    (hL : LawsPi T Dd) (hE : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c) : NuFinAt T Dd :=
  nuFinAt_of T hp Dd hL.wts hE (fun j _ => Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds (T.Q.Xo j) T.Q.c)

end NuFin

end Formalism.L2.Indef.Tree.DepthTie
