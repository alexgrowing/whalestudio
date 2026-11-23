import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_resolution_of_identity : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧ ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  first | exact @GlobalTheory.SelfDualIdDecomp.iddecomp | exact GlobalTheory.SelfDualIdDecomp.iddecomp | (intros; apply GlobalTheory.SelfDualIdDecomp.iddecomp <;> assumption)
