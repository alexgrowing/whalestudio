import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnipMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_radical' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁),
    ∀ (t : (AE F E)ˣ) (a : UA σ X.J), IsLevi (W₁ := X₁) H t 1 a → ∀ n ∈ unip σ X H, a * n * a⁻¹ ∈ unip σ X H := by
  first | exact @GlobalTheory.ThK.LevNorm.conj_unip_mem | exact GlobalTheory.ThK.LevNorm.conj_unip_mem | (intros; apply GlobalTheory.ThK.LevNorm.conj_unip_mem <;> assumption)
