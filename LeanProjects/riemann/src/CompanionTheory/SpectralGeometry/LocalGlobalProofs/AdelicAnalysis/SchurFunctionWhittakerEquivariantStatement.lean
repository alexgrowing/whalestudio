import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionWhittakerEquivariant
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_function_whittaker_equivariant : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ a : ℕ, 0 < a → ∃ Df : A F → ℝ, Continuous Df ∧ (∀ y, 0 ≤ Df y) ∧ (∀ U : Set (A F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i, (a : A F) * x i ∈ Oh F) ∧ qf (hf F) (Bf B) x ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df y) ∂lf) ∧ Integrable (fstar ψ (hf F) (Bf B) (muF B lf) (indL a)) lf ∧ ∀ z : A F, ∫ y, fstar ψ (hf F) (Bf B) (muF B lf) (indL a) y * ψ (-z * y) ∂lf = ((kap F ^ (2 * M - 2) * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * Df z : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Dens.density_main | exact GlobalTheory.CompanionTheory.SW.Core.Dens.density_main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Dens.density_main <;> assumption)
