import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSurjectiveAdelic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_surjective_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s → ∀ z : Fin n → AE F E, ∃ y : Fin n → AE F E, (incM F X.J *ᵥ fun k => cA σ (y k)) = z := by
  first | exact @GlobalTheory.ThK.incM_mulVec_cA_surjective | exact GlobalTheory.ThK.incM_mulVec_cA_surjective | (intros; apply GlobalTheory.ThK.incM_mulVec_cA_surjective <;> assumption)
