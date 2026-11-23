import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagVecMemAndSpan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagVec_mem_Lf_and_inMod : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → (∀ j, flagVec e0 f0 z0 bw bwd j ∈ I.Lf) ∧ ∀ y ∈ I.Lf, InMod I g (Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val) y := by
  first | exact @GlobalTheory.FlagBasis.flagVec_mem_and_span | exact GlobalTheory.FlagBasis.flagVec_mem_and_span | (intros; apply GlobalTheory.FlagBasis.flagVec_mem_and_span <;> assumption)
