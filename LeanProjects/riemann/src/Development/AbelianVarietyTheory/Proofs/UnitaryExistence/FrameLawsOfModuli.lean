import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicPointsModuliEveryPlace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralLatticeStructureUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridgeU
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.ProjectiveLattices.UnifLeaves
import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Exist

theorem frame_laws_of_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (ChartCoverF Xo c ∧ FrChartF Xo c ∧ BorChartF Xo c ∧ IntLatU Xo c ∧ AllTest Xo c ∧ ∀ σ : c.F →+* ℂ, BCEx Xo c σ ∧ WtC Xo c σ) ∧ (1 ≤ Dw.p + Dw.q → Nonempty Xo.X ∧ AlgPtLa Xo c ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrExt Xo c ∧ IntAll Xo c)) := by
  intro E _ _ _ H Dw l Xo c
  have hL := GlobalTheory.lawsFieldsSeparately
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := hL.2.1
  have hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hC := GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hN : N1c := GlobalTheory.closing_of_abelianSchemeLaws
  refine ⟨⟨hC, frChartF_of hC, borChartF_of_cover hC, GlobalTheory.Frames.intLatU_holds E H Dw l Xo c, hA,
    fun σ => ⟨fun p y ψ => ?_, wtC_of (borChartF_of_cover hC) hA σ⟩⟩, fun hpq => ⟨?_,
    GlobalTheory.algPtLa_moduli hN E H Dw l Xo c hpq, fun hg => ⟨?_, ?_⟩⟩⟩
  · exact GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ ψ y
  · obtain ⟨L, _, _, j, x, -⟩ := GlobalTheory.moduli_exists_numberField_point hN E H Dw l Xo c hpq
    exact ⟨x (IsLocalRing.closedPoint L)⟩
  · exact GlobalTheory.Exist.intFrExt_of_good GlobalTheory.partI_closed GlobalTheory.Moduli.moduli_scheme_exists hS hT
      E H Dw l Xo c hpq hg
  · exact (Formalism.L2.PjFree.intAll_iff Xo c).1 (GlobalTheory.IntegralFrames.intAll GlobalTheory.partI_closed
      GlobalTheory.Moduli.moduli_scheme_exists hS hT E H Dw l Xo c hpq hg)

end GlobalTheory.Exist
