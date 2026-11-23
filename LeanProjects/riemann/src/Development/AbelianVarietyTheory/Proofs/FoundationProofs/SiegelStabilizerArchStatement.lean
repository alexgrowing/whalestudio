import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelStabilizerArch
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOne
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_stabilizer_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (h : Q = dblGram finSumFinEquiv J) (w : InfinitePlace F) (τ : EmbOver E w) (b : GL (Fin n) (w.Completion ⊗[F] E)) (g : GArch σ J w) (p : siegelH w.Completion σ Q) (k : GArch σ Q w), k ∈ KArch σ Q w b → ioH w.Completion σ h (g, 1) = p * k → ‖infEmb τ (aH w.Completion σ Q p).1‖ ^ 2 * ‖((2 : ℂ)⁻¹ • (1 + inFrame σ J τ b g * (inFrame σ J τ b g)ᴴ)).det‖ = 1 := by
  first | exact @GlobalTheory.Core.Rk.GraphGram.normSq_aH_mul_gramDet | exact GlobalTheory.Core.Rk.GraphGram.normSq_aH_mul_gramDet | (intros; apply GlobalTheory.Core.Rk.GraphGram.normSq_aH_mul_gramDet <;> assumption)
