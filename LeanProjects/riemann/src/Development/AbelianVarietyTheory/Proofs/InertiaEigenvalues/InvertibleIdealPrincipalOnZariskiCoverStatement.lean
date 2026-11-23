import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealPrincipalOnZariskiCover
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertible_ideal_principal_on_zariski_cover : ∀ (A : Type) [CommRing A] (I : Ideal A), Module.Invertible A ↥I → ∃ (n : ℕ) (s t : Fin n → A), Ideal.span (Set.range s) = ⊤ ∧ ∀ i, t i ∈ I ∧ ∀ x ∈ I, ∃ c, s i * x = c * t i := by
  first | exact @GlobalTheory.BSP.invertible_ideal_principal_on_cover | exact GlobalTheory.BSP.invertible_ideal_principal_on_cover | (intros; apply GlobalTheory.BSP.invertible_ideal_principal_on_cover <;> assumption)
