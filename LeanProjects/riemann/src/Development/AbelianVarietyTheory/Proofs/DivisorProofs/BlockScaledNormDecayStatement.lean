import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledNormDecay
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_scaled_norm_decay : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) → ∀ c : ℝ, 0 < c → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ ξ : κ → F,
      ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) ^ ((q + 1) * N))⁻¹ ≤
        C * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
          (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹ := by
  first | exact @GlobalTheory.ThKTorus.MajCompare.weight_le_majorant | exact GlobalTheory.ThKTorus.MajCompare.weight_le_majorant | (intros; apply GlobalTheory.ThKTorus.MajCompare.weight_le_majorant <;> assumption)
