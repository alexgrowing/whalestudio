import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionEulerProduct
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_modulus_gl_action_product_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (g : GL (Fin M) E), ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (actTup (Ainf F) (bc (inclR (Ainf F)) g)) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (actTup (Fv F v) (bc (inclR (Fv F v)) g)) = c v • μ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PfAct.product_formula_actTup | exact GlobalTheory.CompanionTheory.SW.PfAct.product_formula_actTup | (intros; apply GlobalTheory.CompanionTheory.SW.PfAct.product_formula_actTup <;> assumption)
