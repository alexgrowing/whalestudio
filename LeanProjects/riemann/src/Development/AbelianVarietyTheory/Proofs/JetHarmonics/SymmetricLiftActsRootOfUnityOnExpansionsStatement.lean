import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansions
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (q : ℕ), 1 ≤ q → ∀ (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (s t₀ t : Fam P.D.toPre F q) (x : TFK (R := T.V) F ⟶ P.A.A) (b : ptO Xo xF ⟶ Xo.univ.t.G) (p : QkPt P.D.toPre F q) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F), SecTieF I P F xF q σ hh → SecTieF I P F xF q σ' hh' → P.U.toUnifPre.ExpandsG F q σ s → IsSymAct Xo.univ.t.G Xo.univ.t.PP q b hh hh' → PtTieF I P F xF x b → P.ToA F q p x → w.IsGen → FinOrd P.D F q p w ζ → PhiRel P.D.toPre F q p w s t₀ → Fam.IsSmul P.D.toPre F ζ t₀ t → ∃ (u : F) (t' : Fam P.D.toPre F q), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ Fam.IsSmul P.D.toPre F u t t' ∧ P.U.toUnifPre.ExpandsG F q σ' t' := by
  first | exact @GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct | exact GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct | (intros; apply GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct <;> assumption)
