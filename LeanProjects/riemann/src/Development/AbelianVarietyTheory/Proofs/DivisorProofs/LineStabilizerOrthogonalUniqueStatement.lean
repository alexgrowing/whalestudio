import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineStabilizerOrthogonalUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_stabilizer_orthogonal_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ p ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∀ G G' : Matrix (Fin n₁) (Fin n₁) (AE F E), (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (G *ᵥ z) + a • incV F H.x) → (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat p⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (G' *ᵥ z) + a • incV F H.x) → ∃ g₀ : UA σ X₁.J, mat g₀ = G := by
  first | exact @GlobalTheory.IwUnitaryPart.unitary_part | exact GlobalTheory.IwUnitaryPart.unitary_part | (intros; apply GlobalTheory.IwUnitaryPart.unitary_part <;> assumption)
