import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFunctionalNonvanishing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_functional_nonvanishing : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : Fin n → AE F E),
    (fun k => piW B.τ₁ (c k)) ≠ 0 →
    (∀ z : Fin d → AE F E, At (evFin F B.v₁) z → (∀ l, piW (B.τ₁.comp σ) (z l) = 0) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), Λ (M.co.rho B.ψ (Matrix.vecMulVec c z) Ψ) = Λ Ψ) →
    ∀ Φ ∈ M.So B.ψ B.τ₁, Λ Φ = 0 := by
  first | exact @GlobalTheory.ThKSoKill.so_kill | exact GlobalTheory.ThKSoKill.so_kill | (intros; apply GlobalTheory.ThKSoKill.so_kill <;> assumption)
