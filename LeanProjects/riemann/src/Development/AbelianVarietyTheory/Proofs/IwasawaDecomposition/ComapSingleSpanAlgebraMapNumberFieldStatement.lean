import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapSingleSpanAlgebraMapNumberField
import Mathlib
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comap_single_span_algebraMap_numberField : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι), (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) = Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  first | exact @GlobalTheory.comap_single_span_algebraMap | exact GlobalTheory.comap_single_span_algebraMap | (intros; apply GlobalTheory.comap_single_span_algebraMap <;> assumption)
