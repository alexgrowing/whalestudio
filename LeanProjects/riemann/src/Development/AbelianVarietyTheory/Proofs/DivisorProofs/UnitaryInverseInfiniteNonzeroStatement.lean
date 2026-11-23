import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryInverseInfiniteNonzero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_inverse_infinite_nonzero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) (x : Fin n → E), x ≠ 0 →
    (fun k => piW B.τ₁ ((mat g⁻¹ *ᵥ incV F x) k)) ≠ 0 := by
  first | exact @GlobalTheory.ThKTorus.piW_mat_inv_mulVec_incV_ne_zero | exact GlobalTheory.ThKTorus.piW_mat_inv_mulVec_incV_ne_zero | (intros; apply GlobalTheory.ThKTorus.piW_mat_inv_mulVec_incV_ne_zero <;> assumption)
