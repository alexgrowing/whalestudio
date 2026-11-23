import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleSeesaw
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_triple_seesaw : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∃ L : Submodule F ((Fin (b + 2) × Fin (b + 2 + a') → F) × (Fin (b + 2) × Fin (b + 2 + a') → F)), (∀ p ∈ L, ∀ q ∈ L, p.1 ⬝ᵥ q.2 = q.1 ⬝ᵥ p.2) ∧
      Module.finrank F L = Fintype.card (Fin (b + 2) × Fin (b + 2 + a')) ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ u₁ ∈ iso0 (F := F) (b + 2) H', ∃ u₂ ∈ {u : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E) | ∃ y, u = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y)},
        ∃ z : Matrix (Fin b) (Fin (b + a')) (AE F E), (G₁.M.co.e z).1 = 0 ∧ ∀ φ : Fn F (b + 2) (b + 2 + a'),
          schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
            G.M.co.rho B.ψ u₁ (G.M.co.rho B.ψ u₂ (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) φ)) := by
  first | exact @GlobalTheory.MixedLagrA.lagrangian_isoA | exact GlobalTheory.MixedLagrA.lagrangian_isoA | (intros; apply GlobalTheory.MixedLagrA.lagrangian_isoA <;> assumption)
