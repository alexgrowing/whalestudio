import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairAdaptedPlanes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_pair_adapted_planes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (M₁ : Model σ X₁ W₁),
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ (y : Fin n → AE F E) (z₂ : Fin d₁ → AE F E) (z : Matrix (Fin n₁) (Fin d₁) (AE F E)),
        (M₁.co.e z).1 = 0 ∧ ∀ φ : (Fin n × Fin d → AF F) → ℂ,
          schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
            M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x))
              (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂))
                (M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) φ)) := by
  first | exact @GlobalTheory.MixedLagrXW.exists_ratLagr | exact GlobalTheory.MixedLagrXW.exists_ratLagr | (intros; apply GlobalTheory.MixedLagrXW.exists_ratLagr <;> assumption)
