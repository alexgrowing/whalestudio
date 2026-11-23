import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusContractingBlockLtOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_contracting_block_lt_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one | exact GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one | (intros; apply GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one <;> assumption)
