import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriangularFrameEigenScalar
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_frame_eigen_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → ℂ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ eb e τ i = h (∑ j, cf j • eb e τ j)) → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), (∀ j, j ≤ i) → ∃ y : ℂ, ∀ w, h w (e.symm ⟨τ, i⟩) = y * w (e.symm ⟨τ, i⟩) := by
  first | exact @GlobalTheory.eigenCoord_top_of_triangular | exact GlobalTheory.eigenCoord_top_of_triangular | (intros; apply GlobalTheory.eigenCoord_top_of_triangular <;> assumption)
