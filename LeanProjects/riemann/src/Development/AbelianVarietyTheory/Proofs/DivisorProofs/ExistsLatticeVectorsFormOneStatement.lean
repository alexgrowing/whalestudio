import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorsFormOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_vectors_form_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → 0 < n →
    ∃ (m : ℕ) (x y : Fin m → Fin n → E), (∀ i, x i ∈ X.L ∧ y i ∈ X.L) ∧ ∑ i, form σ X.J (x i) (y i) = 1 := by
  first | exact @GlobalTheory.FormOne.exists_sum_form_eq_one | exact GlobalTheory.FormOne.exists_sum_form_eq_one | (intros; apply GlobalTheory.FormOne.exists_sum_form_eq_one <;> assumption)
