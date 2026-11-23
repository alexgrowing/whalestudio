import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineStabilizerModulusHaar
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
theorem _root_.GlobalTheory.T.line_stabilizer_modulus_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ μP : Measure (lineStab σ X H.x), μP.IsHaarMeasure → ∀ (p : lineStab σ X H.x) (t : (AE F E)ˣ),
      mat p.1.1 *ᵥ incV F H.x = t.1 • incV F H.x → μP.map (· * p) = (absE F E t ^ (n₁ + 1)) • μP := by
  first | exact @GlobalTheory.ArchLineModulus.map_mul_right_lineStab | exact GlobalTheory.ArchLineModulus.map_mul_right_lineStab | (intros; apply GlobalTheory.ArchLineModulus.map_mul_right_lineStab <;> assumption)
