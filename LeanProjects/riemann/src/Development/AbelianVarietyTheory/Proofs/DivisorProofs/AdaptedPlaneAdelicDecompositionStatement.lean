import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneAdelicDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_adelic_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ : ℕ), Y.L.IsLattice E →
    H.IsAdapted σ B Y Y₁ i₀ i₁ → ∀ w : Fin n → AE F E, ∃ (α β : AE F E) (z : Fin n₁ → AE F E),
      w = α • incV F H.x + incM F H.ι *ᵥ z + β • incV F H.y := by
  first | exact @GlobalTheory.ThK.LemF.QuotInv.AdSpan.adelic_span | exact GlobalTheory.ThK.LemF.QuotInv.AdSpan.adelic_span | (intros; apply GlobalTheory.ThK.LemF.QuotInv.AdSpan.adelic_span <;> assumption)
