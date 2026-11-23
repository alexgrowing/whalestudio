import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralAdeleCongrZeroOfResiduesSquarefree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree : ∀ (I : AutInst) (g : ℕ), g ≠ 0 → (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → (g : 𝓞 I.E) ∉ Q.asIdeal ^ 2) → ∀ s : Formalism.L2.Herm.intAf I.F I.E, (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → resS I.F Q s = 0) → ZMod' I g s := by
  first | exact @GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero | exact GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero | (intros; apply GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero <;> assumption)
