import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCompletion_moves_by_translatePair : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (g s : GA D S) (h s' : GA D T) N N' N₁ N₁', Moves S hS g N → Moves T hT h N' → Moves S hS (s * g) N₁ → Moves T hT (s' * h) N₁' → ∀ u : WO S T, u ∈ (latO S T (latFr S hS N₁) (latFr T hT N₁') fun _ => True) ↔ ∃ u₀ ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), u = actO S T s s' u₀ := by
  first | exact @GlobalTheory.LatPairMove.latO_move | exact GlobalTheory.LatPairMove.latO_move | (intros; apply GlobalTheory.LatPairMove.latO_move <;> assumption)
