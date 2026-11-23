import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterleavingTwoColourEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClOfSelf
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interleaving_two_colour_embedding : ∀ {T : Type 1} {u v w : List T}, Zc.Comb.Interleave u v w → ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length) (σ₁ : Fin v.length ↪o Fin w.length), (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧ (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings | exact GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings | (intros; apply GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings <;> assumption)
