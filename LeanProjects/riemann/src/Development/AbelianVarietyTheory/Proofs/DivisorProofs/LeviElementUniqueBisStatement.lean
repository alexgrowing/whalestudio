import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueBis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_element_unique_bis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (h₁ : UA σ X₁.J) (h h' : UA σ X.J), IsLevi (W₁ := X₁) H t h₁ h → IsLevi (W₁ := X₁) H t h₁ h' → h = h' := by
  first | exact @GlobalTheory.LeviUniqueGen.levi_unique_gen | exact GlobalTheory.LeviUniqueGen.levi_unique_gen | (intros; apply GlobalTheory.LeviUniqueGen.levi_unique_gen <;> assumption)
