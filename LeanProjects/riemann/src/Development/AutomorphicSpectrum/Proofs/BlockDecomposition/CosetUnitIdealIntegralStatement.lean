import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegral
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_unit_ideal_integral : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | exact GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top <;> assumption)
