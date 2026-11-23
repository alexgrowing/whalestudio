import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionEnlargeFiniteSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_function_enlarge_finite_set : ∀ (F : Type) [Field F] [NumberField F] (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)),
    IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    (∫ y, phiA G a y ∂(Measure.pi fun _ : Unit => li)) * ∏ v ∈ T, ∫ y, psiA S g a v y ∂(Measure.pi fun _ : Unit => lam v) =
      (md a)⁻¹ * ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v)) := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.Integrals.integrals_translates | exact GlobalTheory.CompanionTheory.BasePsi.Integrals.integrals_translates | (intros; apply GlobalTheory.CompanionTheory.BasePsi.Integrals.integrals_translates <;> assumption)
