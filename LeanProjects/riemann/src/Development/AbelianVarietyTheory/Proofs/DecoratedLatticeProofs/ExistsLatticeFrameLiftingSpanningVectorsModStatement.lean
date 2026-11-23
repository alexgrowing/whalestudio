import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeFrameLiftingSpanningVectorsMod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod : ∀ (D : D7) (g : ℕ), g ≠ 0 → ∀ b : ℕ → VA (instOf D), (∀ j, b j ∈ (instOf D).Lf) → (∀ y ∈ (instOf D).Lf, InMod (instOf D) g (Set.range fun j : Fin (instOf D).n => b j.val) y) → ∃ β, IsLiftFrame (instOf D) g b β := by
  first | exact @GlobalTheory.LiftFrameMod.exists_isLiftFrame | exact GlobalTheory.LiftFrameMod.exists_isLiftFrame | (intros; apply GlobalTheory.LiftFrameMod.exists_isLiftFrame <;> assumption)
