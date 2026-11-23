import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleMatchedFold
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_A_triple_matched_fold : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ y : Fin b × Fin (b + a') → AF F, ∀ (m : ℕ) (b₀ : Module.Basis (Fin m) F E) (N : ℕ), ∃ C : ℝ, ∀ a, ‖(fun a : AE F E => e (G.M.co.rho B.ψ (a • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Φ) y) a‖ * (1 + ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun a i)‖) ^ N ≤ C := by
  first | exact @GlobalTheory.ConeTateDecay.decay | exact GlobalTheory.ConeTateDecay.decay | (intros; apply GlobalTheory.ConeTateDecay.decay <;> assumption)
