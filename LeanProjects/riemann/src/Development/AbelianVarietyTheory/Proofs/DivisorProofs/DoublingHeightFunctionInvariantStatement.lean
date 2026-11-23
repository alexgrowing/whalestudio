import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingHeightFunctionInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_height_function_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n r s' : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s' →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → (∀ k ∈ K, hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (k, 1)) = 1) ∧
      ∀ (T : Finset (Pl F)) (g : UA σ X.J), (∀ v ∉ T, compAt σ X.J v g ∈ K) →
        hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1)) =
          hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (compArch σ X.J g, 1)) *
            ∏ v ∈ T, hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (compAt σ X.J v g, 1)) := by
  first | exact @GlobalTheory.ThK.Bot.HgtMul.hgt_one_and_mul | exact GlobalTheory.ThK.Bot.HgtMul.hgt_one_and_mul | (intros; apply GlobalTheory.ThK.Bot.HgtMul.hgt_one_and_mul <;> assumption)
