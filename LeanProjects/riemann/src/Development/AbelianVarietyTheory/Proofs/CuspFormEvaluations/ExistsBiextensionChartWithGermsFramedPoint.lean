import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.LocalToGlobal.ProjectiveLattices.ThExpBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsChartGOfBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesOfFormalChart
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ChartRing

theorem bijective_appTop_powObj (hGF : GlobalFnsSt) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsAbelianScheme G) (n : ℕ) :
    Function.Bijective (ReciprocityTheory.ChartRestriction.G.Out.powObj G n).hom.appTop.hom := by
  cases n with
  | zero =>
    show Function.Bijective (𝟙 S : S ⟶ S).appTop.hom
    simp only [Scheme.Hom.id_appTop, CommRingCat.hom_id]
    exact Function.bijective_id
  | succ n => exact hGF _ _ (AbelianSchemeGerms.isAbelianScheme_powObj G hG n)

set_option maxHeartbeats 1600000 in

theorem exists_chartAt_with_germs : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S), ∃ C : ChartAt Xo c y, FrTruncC y C ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f := by
  intro hL E _ _ _ H Dw l Xo c _ hstar S _ _ _ y
  obtain ⟨d, G, A, uvec, x, -, -, hchG⟩ :=
    GlobalTheory.ChartData.exists_isChartG_of_basis E H Xo.X Xo.univ.t S y.x (Lt1 Dw) (fun ℓ => y.u ℓ.1 ℓ.2)
      (fun ℓ => y.tan ℓ.1 ℓ.2) (fun w hw => GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c S y w hw)
  have hch := (isChart_iff y d G.F A.act uvec x).2 hchG
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    GlobalTheory.exists_frames_of_chart E H Xo.X Xo.univ.t S y.x d G A (Lt1 Dw) _ uvec x hchG
  have hPow := bijective_appTop_powObj hL.globalFns Xo.univ.t.G (GlobalTheory.moduli_univ_polAV E H Dw l Xo).2.2.2.1
  obtain ⟨hax, hr⟩ := GlobalTheory.FrameBiextId.fbId E H Xo.X Xo.univ.t hPow hstar S y.x d G A (Lt1 Dw) _ uvec x e
    ph1 ph2 sy ad hchG hfr hfa had
  obtain ⟨h, hh⟩ := GlobalTheory.canonGauge_exists S d (𝓞 E) S (mkFB G A ph1 ph2 sy ad hax hr)
  refine ⟨⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, h, hch,
    (isFrame_iff y d x _ _ _ _ _ _ e).2 hfr, (isPrim_iff wP).2 hpr, hh, hrig⟩, htr, ?_⟩
  intro k F
  obtain ⟨f, hf⟩ := germSt_holds E H Xo.X Xo.univ.t S y.x d G.F A.act (Lt1 Dw) _ uvec x ph1 ph2 sy ad e wP
    hchG hfr hpr htr k F
  exact ⟨f, (isGerm_iff y d x _ e wP k F f).2 hf⟩

end GlobalTheory.ChartRing
