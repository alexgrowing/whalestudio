import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentProductDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_unipotent_product_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ (t : (AE F E)ˣ) (a : UA σ X.J) (g₀ : UA σ X₁.J) (g' : UA σ X.J),
    IsLevi (W₁ := X₁) H t 1 a → IsLevi H 1 g₀ g' → a * g' = g' * a := by
  first | exact @GlobalTheory.LeviComm.levi_comm | exact GlobalTheory.LeviComm.levi_comm | (intros; apply GlobalTheory.LeviComm.levi_comm <;> assumption)
