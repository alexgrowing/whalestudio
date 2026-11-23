import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdeleIsoComponentZeroOfInfinitelyDivisible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdele_iso_component_zero_of_infinitely_divisible : ∀ {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E), (∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1) → (∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E') → ∀ (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E'), GlobalTheory.TwU.IsAdIso ι → ∀ (z : AfE F E) (ℓ D : ℕ), 0 < ℓ → 0 < D → (∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E) → ∀ (P : HeightOneSpectrum (𝓞 E')), ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal → ι (iA.symm z) P = 0 := by
  first | exact @GlobalTheory.TwV.Xc.adIso_comp_zero_of_div | exact GlobalTheory.TwV.Xc.adIso_comp_zero_of_div | (intros; apply GlobalTheory.TwV.Xc.adIso_comp_zero_of_div <;> assumption)
