import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFormMemInverseDifferent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_form_mem_inverse_different : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d d₁ r s j₀ j₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁),
    Plane.IsAdapted σ B H' W W₁ j₀ j₁ → Spc.IsSkew σ B W r s →
      ∀ y ∈ W.L, form σ W.J y H'.x ∈ (conjI σ H'.𝔟)⁻¹ * (diffE E)⁻¹ := by
  first | exact @GlobalTheory.PairDual.form_mem_conjI_inv_mul_diffE_inv | exact GlobalTheory.PairDual.form_mem_conjI_inv_mul_diffE_inv | (intros; apply GlobalTheory.PairDual.form_mem_conjI_inv_mul_diffE_inv <;> assumption)
