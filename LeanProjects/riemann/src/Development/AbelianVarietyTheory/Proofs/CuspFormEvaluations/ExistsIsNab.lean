import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.LocalToGlobal.ProjectiveLattices.ThExpBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBiextensionChartWithGermsFramedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.CanonConn

theorem exists_isNab : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab := by
  intro hL E _ _ _ H Dw l Xo c
  classical
  letI : StarRing (𝓞 E) := H.starRing
  have hs : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hC := GlobalTheory.T.exists_biextension_chart_with_germs_framed_point hL E H Dw l Xo c hs
  choose C _hT hg using hC
  choose g hg using hg
  let val : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (k : ℤ),
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)) → (Lt1 Dw →₀ ℕ) → S :=
    fun S _ _ _ y k => match k with
      | Int.ofNat k => fun F α =>
          (C S y).B.nabVal S (C S y).h H.w0 k (g S y k F) (C S y).uvec (MvPolynomial.monomial α 1)
      | Int.negSucc _ => fun _ _ => 0
  let nab : NabV Xo c := fun {S} _ _ y k F α =>
    if h : Nonempty (Algebra ℚ S) then @val S _ _ h.some y k F α else 0
  refine ⟨inferInstance, nab, hs, ?_⟩
  intro S _ _ iQ y
  refine ⟨C S y, fun k F => ⟨_, hg S y k F⟩, ?_⟩
  intro k F f hf α
  have hne : Nonempty (Algebra ℚ S) := ⟨iQ⟩
  have h1 : nab y k F α = @val S _ _ hne.some y k F α := dif_pos hne
  have h2 : hne.some = iQ := Subsingleton.elim _ _
  refine h1.trans ?_
  rw [h2, isGermFun_holds E H Dw l Xo c S y _ _ _ _ _ k F f _ hf (hg S y k F)]

end GlobalTheory.CanonConn
