import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastBlockCentralScalarModulusOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_block_central_scalar_modulus_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h), j.val + 1 = h → leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = Matrix.GeneralLinearGroup.scalar (Fin N) t ∧ modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.ZjScalar.zj_last_scalar_modulus | exact GlobalTheory.CompanionTheory.ZjScalar.zj_last_scalar_modulus | (intros; apply GlobalTheory.CompanionTheory.ZjScalar.zj_last_scalar_modulus <;> assumption)
