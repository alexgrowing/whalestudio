import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralLatticeStructureUniqueStatement

noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem algebraic_laws : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrChartF Xo c ∧ BorChartF Xo c ∧ EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ WtField Xo c ∧ IntDiagUnit Xo c ∧ UnitIndep Xo c ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S], IsReduced S → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y := by
  intro hB E _ _ _ H Dw l Xo c

  have hTest := GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c
  have hCov := GlobalTheory.T.chartCoverF_of_sectionBaseChange hB E H Dw l Xo c
  have hLat := GlobalTheory.T.integralLattice_structure_unique E H Dw l Xo c
  have hFr : FrChartF Xo c := frChartF_of hCov
  have hBor : BorChartF Xo c := borChartF_of_cover hCov
  refine ⟨hFr, hBor, evalWD_fr hFr, wtField_of_borChart hBor, intDiagUnit_of hLat,
    unitIndep_of_charts hBor hLat, ?_⟩

  intro S _ _ hS a n f hf t y y' hy
  obtain ⟨hnat, hwt⟩ := hf
  exact wtAll_of_borChart hBor (ex Dw a n) hnat hwt S t y y' (hTest S y) (hTest S y') hy

end GlobalTheory.Frames
