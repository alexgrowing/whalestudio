import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfFlatTower
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.FlatL
open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lseq_of_flat_tower : ∀ (W : Type) [CommRing W] (l : ℕ) (Kt : ℕ → Cx.{1} W) (ψ : ∀ n, Cx.Hom (Kt n) (quo l (Kt (n + 1)) n) (RingHom.id W)) (hψ : ∀ n j, Function.Bijective ((ψ n).mapH j)), (∀ c, FlatL l c (Kt c)) → (∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j)) → ∀ j, Nonempty (LSeq l (tsys l Kt ψ hψ j) (tsys l Kt ψ hψ (j + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys | exact GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys | (intros; apply GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys <;> assumption)
