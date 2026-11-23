import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfSpanOfStrict
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicTopologicalBasis_of_span_of_strict : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 → I.FG → IsAdicComplete I S → IsAdicComplete (I.map s) A → (∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) → (∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n) → ∃ TB : TopBasis s I ι, TB.b = b := by
  first | exact @GlobalTheory.BSP.exists_topBasis_of_span_of_strict | exact GlobalTheory.BSP.exists_topBasis_of_span_of_strict | (intros; apply GlobalTheory.BSP.exists_topBasis_of_span_of_strict <;> assumption)
