import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanMaxCompactContained
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_max_compact_contained : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      (∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) → ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∃ K, IsMaxCpt σ (c • Y.J.map σ) K ∧ ∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb := by
  first | exact @GlobalTheory.ThK.SqIntMaxCptGen.exists_isMaxCpt_le_kInf_of_cartan | exact GlobalTheory.ThK.SqIntMaxCptGen.exists_isMaxCpt_le_kInf_of_cartan | (intros; apply GlobalTheory.ThK.SqIntMaxCptGen.exists_isMaxCpt_le_kInf_of_cartan <;> assumption)
