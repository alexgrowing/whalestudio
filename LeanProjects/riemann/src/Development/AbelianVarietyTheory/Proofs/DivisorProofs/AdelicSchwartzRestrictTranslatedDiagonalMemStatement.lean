import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMem
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_restrict_translated_diagonal_mem : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → ∀ u : κ → AF F, (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi F κ := by
  first | exact @GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi | exact GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi | (intros; apply GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi <;> assumption)
