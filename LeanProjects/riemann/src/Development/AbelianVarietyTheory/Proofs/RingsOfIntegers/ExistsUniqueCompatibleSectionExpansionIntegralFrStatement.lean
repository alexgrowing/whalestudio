import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueCompatibleSectionExpansionIntegralFr
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_compatibleSection_expansion_integralFramedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ k : ℕ, 1 ≤ k → ∀ hh : SecN Xo xF k, (∃! σ, SecTieF I P F xF k σ hh) ∧ ∀ σ, SecTieF I P F xF k σ hh → ∃! s, P.U.toUnifPre.ExpandsG F k σ s := by
  first | exact @GlobalTheory.tied_section_expansion_existsUnique | exact GlobalTheory.tied_section_expansion_existsUnique | (intros; apply GlobalTheory.tied_section_expansion_existsUnique <;> assumption)
