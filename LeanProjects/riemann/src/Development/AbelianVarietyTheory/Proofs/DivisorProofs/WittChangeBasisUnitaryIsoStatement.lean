import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittChangeBasisUnitaryIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_change_basis_unitary_iso : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∃ κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n, IsChartW T κ := by
  first | exact @GlobalTheory.SWLinkChart.exists_isChartW | exact GlobalTheory.SWLinkChart.exists_isChartW | (intros; apply GlobalTheory.SWLinkChart.exists_isChartW <;> assumption)
