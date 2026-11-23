import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_automorphic_criterion : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ) → ∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ z ∈ Zalg E a, ∀ g, (z F).1 g = ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg | exact GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg | (intros; apply GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg <;> assumption)
