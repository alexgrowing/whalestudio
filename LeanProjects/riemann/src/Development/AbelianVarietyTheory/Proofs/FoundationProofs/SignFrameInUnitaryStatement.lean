import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameInUnitary
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOne
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sign_frame_in_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)), IsSignFrame σ J ε b → ∀ g : GArch σ J w, IsInU ε (inFrame σ J τ b g) := by
  first | exact @GlobalTheory.Core.SignFrame.isInU_inFrame | exact GlobalTheory.Core.SignFrame.isInU_inFrame | (intros; apply GlobalTheory.Core.SignFrame.isInU_inFrame <;> assumption)
