import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicLineStabilizerDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLineStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.IwasawaKAvgInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_line_stabilizer_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ K : Subgroup (UA σ X.J), IsStab B K →
    ∀ g ∈ UAt σ X (evI F), ∃ p ∈ UAt σ X (evI F), (∃ t : (AE F E)ˣ, mat p *ᵥ incV F H.x = t.1 • incV F H.x) ∧
      ∃ k ∈ KAt K (evI F), g = p * k := by
  first | exact @GlobalTheory.IwasawaInf.exists_stab_mul_KAt | exact GlobalTheory.IwasawaInf.exists_stab_mul_KAt | (intros; apply GlobalTheory.IwasawaInf.exists_stab_mul_KAt <;> assumption)
