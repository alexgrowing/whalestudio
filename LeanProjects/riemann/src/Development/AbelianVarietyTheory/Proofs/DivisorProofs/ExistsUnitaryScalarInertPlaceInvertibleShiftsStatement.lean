import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalarInertPlaceInvertibleShifts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryScalar_inertPlace_invertible_shifts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J),
    ∃ k : UA σ J, At (evFin F v) (mat k - 1) ∧ ∃ a b : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) a ∧ At (evFin F v) b ∧
      a * (1 - mat k) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      (1 - mat k) * a = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      b * (1 - mat (g⁻¹ * k)) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      (1 - mat (g⁻¹ * k)) * b = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  first | exact @GlobalTheory.InertScalarUnit.exists_scalar_inv_at | exact GlobalTheory.InertScalarUnit.exists_scalar_inv_at | (intros; apply GlobalTheory.InertScalarUnit.exists_scalar_inv_at <;> assumption)
