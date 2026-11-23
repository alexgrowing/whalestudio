import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTraceFormCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_trace_form_coordinates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∃ p q : (Fin n → AE F E) ≃ₗ[AF F] (Fin n × Fin 2 → AF F),
      (∀ a b, p b ⬝ᵥ q a = Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, b i * incM F J i k * cA σ (a k))) ∧
      (∀ a b, p b ⬝ᵥ q a = Algebra.trace (AF F) (AE F E) (∑ i, ∑ k, a i * incM F J i k * cA σ (b k))) ∧
      (∀ a : Fin n → E, ∃ y : Fin n × Fin 2 → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin n → E, ∃ y : Fin n × Fin 2 → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  first | exact @GlobalTheory.HermCoords.exists_herm_pair_coords | exact GlobalTheory.HermCoords.exists_herm_pair_coords | (intros; apply GlobalTheory.HermCoords.exists_herm_pair_coords <;> assumption)
