import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactDoublingProductDecomp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_maximal_compact_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' → min r s' = 0 →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ k ∈ KInf σ X₂ B.emb, ∃ k₁ ∈ KInf σ X B.emb, ∃ k₂ ∈ KInf σ X B.emb, k = i (k₁, k₂) := by
  first | exact @GlobalTheory.DefDblCompact.exists_blocks_of_kInf | exact GlobalTheory.DefDblCompact.exists_blocks_of_kInf | (intros; apply GlobalTheory.DefDblCompact.exists_blocks_of_kInf <;> assumption)
