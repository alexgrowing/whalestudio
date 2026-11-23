import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviChartBlockDiagonalAdjoint
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
theorem _root_.GlobalTheory.T.levi_chart_block_diagonal_adjoint : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ p : siegelOf finSumFinEquiv (uinc D J₂), (p : UD D J₂) ∈ leviSubOf finSumFinEquiv (uinc D J₂) → GlobalTheory.StdUnn.mat (κ p) = GlobalTheory.StdUnn.blk4 (leviOf finSumFinEquiv (uinc D J₂) p).1 0 0 (adj ((leviOf finSumFinEquiv (uinc D J₂) p)⁻¹).1)) ∧ ∀ b ∈ unipOf finSumFinEquiv (uinc D J₂), ∃ β : Mx D n n, GlobalTheory.StdUnn.mat (κ b) = GlobalTheory.StdUnn.blk4 1 β 0 1 := by
  first | exact @GlobalTheory.SWLink.LeviChart.levi_unip_chart | exact GlobalTheory.SWLink.LeviChart.levi_unip_chart | (intros; apply GlobalTheory.SWLink.LeviChart.levi_unip_chart <;> assumption)
