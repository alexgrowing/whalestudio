import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockCentralElementCommutesLevi
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_central_element_commutes_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h), ∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * y = y * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) := by
  first | exact @GlobalTheory.CompanionTheory.ZjCentral.leviEmb_zj_comm | exact GlobalTheory.CompanionTheory.ZjCentral.leviEmb_zj_comm | (intros; apply GlobalTheory.CompanionTheory.ZjCentral.leviEmb_zj_comm <;> assumption)
