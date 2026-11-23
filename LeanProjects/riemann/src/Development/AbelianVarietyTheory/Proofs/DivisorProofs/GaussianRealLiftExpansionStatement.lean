import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianRealLiftExpansion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_real_lift_expansion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.ActsLaws →
    ∀ f₀ : SInf F (Fin n × Fin d), f₀ ≠ 0 → M.IsGauss B.ψ B.emb f₀ →
    ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℂ)
      (z : ℂ), (∀ x, x ≠ 0 → 0 < (Q x x).re) ∧ ∀ x, f₀ x = z * Complex.exp (-(Q x x)) := by
  first | exact @GlobalTheory.VacGauss.fock_vacuum_gaussian | exact GlobalTheory.VacGauss.fock_vacuum_gaussian | (intros; apply GlobalTheory.VacGauss.fock_vacuum_gaussian <;> assumption)
