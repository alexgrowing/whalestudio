import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeOfMemSpan
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraNodesFarApartOfCubicNodeGap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepRealThetaRuleOfNodesFarApart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTestLatUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowEx

theorem baseEx_of (hP : GlobalTheory.FunPr.Hypotheses₂) (hC : ConstEx) : BaseEx := by
  obtain ⟨CF0, hC⟩ := hC
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have hQ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS
  intro G W hW S₀
  obtain ⟨rm, c, hrm, hc⟩ := hQ G W hW S₀.B
  have hL := hS.core.lev
  obtain ⟨M, hM⟩ := exists_vol G hL A.μ0
  obtain ⟨n, e, -, -, -, -⟩ := TestLatModel.exists_testLat (G := G)
    (node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩).sd.1.fg default
  obtain ⟨Pm, -, -⟩ := hS.size.1
  have hCh : ∀ k, GlobalTheory.Chain.ChainPar D k := GlobalTheory.Corev.ChainParOfGap.chainPar_of_nodeGap D
    (GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap D (by simpa using Pm.nodeGap_ge_cubic_rank))
  obtain ⟨cv, hcv⟩ := GlobalTheory.RowTest.WVec.exists_w_ne hP.discreteSeriesCover hP.harishChandraModules hCh R hL
    hS.core.chain hS.core.models.inf
  obtain ⟨S'⟩ := sumChoice_nonempty W S₀ hS.core.fam.tie (GlobalTheory.ForcedWeights.lamRForced D)
  exact ⟨M, fun _ => 0, 0, cv, rm, { S' with toGridChoice := S₀ }, default, n, e, c, rfl,
    ⟨guard_of_qGuard hS.guard, hW, hM.isRow, hrm, hcv, hc⟩⟩

end GlobalTheory.RowEx

end
