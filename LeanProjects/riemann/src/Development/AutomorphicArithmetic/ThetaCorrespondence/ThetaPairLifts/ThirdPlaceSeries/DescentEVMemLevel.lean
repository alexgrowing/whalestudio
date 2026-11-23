import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentEVMemLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem descent_eV_mem_level_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → _root_.GlobalTheory.MiS.LevelHypothesis W → (∀ t F, (_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EEl true) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB hLv t F
  obtain ⟨-, -, -, hC, -⟩ := hB.hyp
  obtain ⟨⟨s, hs⟩, hRZ, gE, hU, hG, h2, hl0, hl1⟩ := hLv
  have hK := RealDat3.kFormR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hJ := RealDat3.jIsoR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hDn := Formalism.IndefR.CxPass.descent_of_types hs hK hJ hRZ hU hG h2 hl0 hl1 true
  have hE := Formalism.IndefR.Links.EvTie.evTie_real ⟨s, hs⟩ W.Q.Rl W.Q.F
  have hV : (_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).V0C W.Q.F.cv true t :=
    Submodule.subset_span ⟨_, hE.1 t F, rfl⟩
  exact hDn t (Submodule.mem_map_of_mem hV)
end GlobalTheory.MiTop
end
end
