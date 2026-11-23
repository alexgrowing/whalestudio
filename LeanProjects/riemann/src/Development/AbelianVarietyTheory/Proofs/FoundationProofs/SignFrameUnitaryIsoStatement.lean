import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIso
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sign_frame_unitary_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)), GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b → ∃ Θ : GArch σ J w ≃ₜ* Formalism.BasicNotions.UpqT (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε), ∀ g, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = Matrix.reindex (Formalism.BasicNotions.Examples₂.CD.e0 ε) (Formalism.BasicNotions.Examples₂.CD.e0 ε) (Formalism.BasicNotions.UpqT.mat (Θ g)) := by
  first | exact @GlobalTheory.FrameIsoReal.exists_frameIso | exact GlobalTheory.FrameIsoReal.exists_frameIso | (intros; apply GlobalTheory.FrameIsoReal.exists_frameIso <;> assumption)
