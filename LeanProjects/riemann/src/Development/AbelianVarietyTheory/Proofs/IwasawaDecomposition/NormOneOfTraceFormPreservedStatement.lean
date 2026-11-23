import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneOfTraceFormPreserved
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_of_trace_form_preserved : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (hr : 0 < r) (ζ : E), (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, Algebra.trace ℚ E (-X.ξ0 * (ζ * cc ζ * herm X.Gm u v)) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm u v)) → ζ * cc ζ = 1 := by
  first | exact @GlobalTheory.trace_form_scalar_norm_one | exact GlobalTheory.trace_form_scalar_norm_one | (intros; apply GlobalTheory.trace_form_scalar_norm_one <;> assumption)
