import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_orthogonalEmbedding_le_pow : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a := by
  first | exact @GlobalTheory.EmbHeight.height_emb_le | exact GlobalTheory.EmbHeight.height_emb_le | (intros; apply GlobalTheory.EmbHeight.height_emb_le <;> assumption)
