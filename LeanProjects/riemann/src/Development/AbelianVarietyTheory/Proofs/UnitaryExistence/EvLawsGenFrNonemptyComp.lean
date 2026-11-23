import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
private theorem nonempty_irreducibleComponents_of_point {X : Type*} [TopologicalSpace X] (x : X) :
    Nonempty (irreducibleComponents X) :=
  ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Reg.evLaws_genFr_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c ∧ _root_.Formalism.L2.Pj.IntDiagUnit Xo c ∧ _root_.Formalism.L2.Pj.GenFrEx Xo c ∧
      (1 ≤ Dw.p + Dw.q → Nonempty (_root_.Formalism.L2.Pj.Comp Xo c)) := by
  intro E _ _ _ H Dw l Xo c
  have hsec : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := _root_.GlobalTheory.allSixLaws.1.secBaseChange
  have htw : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := _root_.GlobalTheory.allSixLaws.2.1.secTwist
  obtain ⟨-, -, hwd, hwt, hdiag, -, -⟩ :=
    _root_.GlobalTheory.Frames.algebraic_laws hsec E H Dw l Xo c
  refine ⟨⟨hwd, _root_.GlobalTheory.Frames.allTest_of_secBaseChange hsec E H Dw l Xo c, hwt, ?_⟩, hdiag,
    _root_.Formalism.L2.Pj.genFrEx_of htw, ?_⟩
  · intro S T _ _ _ _ φ y
    exact _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hsec E H Dw l Xo c S T φ y
  · intro hpq
    obtain ⟨x⟩ := (_root_.GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2
      _root_.GlobalTheory.closing_of_abelianSchemeLaws hpq l Xo c
    unfold _root_.Formalism.L2.Pj.Comp
    exact nonempty_irreducibleComponents_of_point x

end GlobalTheory.Reg
