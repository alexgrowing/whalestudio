import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_center_action_smooth_form : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ z ∈ Zalg E a, ∀ c : Sm E a, c.1 = (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → (z c).1 = fun g : GA E a => ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.ConstTermZalg.constTerm_zalg | exact GlobalTheory.ConstTermZalg.constTerm_zalg | (intros; apply GlobalTheory.ConstTermZalg.constTerm_zalg <;> assumption)
