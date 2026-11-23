import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlacesIdempotentMulAbsorb
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_idempotent_mul_absorb : ∀ {F : Type} [Field F] [NumberField F] {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}, IsPlacesIdem A₁ A₂ a → IsPlacesIdem B₁ B₂ b → A₁ ⊆ B₁ → A₂ ⊆ B₂ → b * a = a := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.idem_mul_eq_of_subset | exact GlobalTheory.CompanionTheory.SaGen.idem_mul_eq_of_subset | (intros; apply GlobalTheory.CompanionTheory.SaGen.idem_mul_eq_of_subset <;> assumption)
