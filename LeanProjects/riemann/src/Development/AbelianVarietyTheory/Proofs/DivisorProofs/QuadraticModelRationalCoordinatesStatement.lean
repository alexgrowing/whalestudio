import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticModelRationalCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_model_rational_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → Module.finrank F E = 2 → ∃ Φ : Matrix (Fin n) (Fin d) E ≃ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x, M.co.e (incM F x) = ((fun i => algebraMap F (AF F) ((Φ x).1 i)), (fun i => algebraMap F (AF F) ((Φ x).2 i))) := by
  first | exact @GlobalTheory.RatCoord.ratEquiv | exact GlobalTheory.RatCoord.ratEquiv | (intros; apply GlobalTheory.RatCoord.ratEquiv <;> assumption)
