import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsMultiplicativeConjugation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_multiplicative_conjugation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin (m + 2)) (Fin (m + 2)) E) (H : Plane E (m + 2) m),
    IsUnit (basQ H).det → (∀ g h : UA σ J, crd H (g * h) = crd H g * crd H h) ∧ crd H (1 : UA σ J) = 1 ∧
      ∀ g : UA σ J, mat g = incM F (basQ H) * (crd H g).submatrix (ixE m) (ixE m) * (incM F (basQ H))⁻¹ := by
  first | exact @GlobalTheory.QhtUnip.crd_mul_one_mat | exact GlobalTheory.QhtUnip.crd_mul_one_mat | (intros; apply GlobalTheory.QhtUnip.crd_mul_one_mat <;> assumption)
