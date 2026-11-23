import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanEigenvectorIdeleMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_eigenvector_idele_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ : ℕ),
    H.IsAdapted σ B X X₁ i₀ i₁ → ∀ p ∈ UAt σ X (evI F), ∀ t : (AE F E)ˣ,
    mat p *ᵥ incV F H.x = t.1 • incV F H.x → t ∈ idelesAt E (evI F) := by
  first | exact @GlobalTheory.ThK.LemF.IwasawaScal.idele_mem_idelesAt_inf | exact GlobalTheory.ThK.LemF.IwasawaScal.idele_mem_idelesAt_inf | (intros; apply GlobalTheory.ThK.LemF.IwasawaScal.idele_mem_idelesAt_inf <;> assumption)
