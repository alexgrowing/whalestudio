import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallIntegralInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_I_smul_left_eq : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), G.M'.I om' (om' (g, 1) Φ) h = G.M'.I om' Φ h := by
  first | exact @GlobalTheory.ThetaAdelicInv.small_integral_invariant | exact GlobalTheory.ThetaAdelicInv.small_integral_invariant | (intros; apply GlobalTheory.ThetaAdelicInv.small_integral_invariant <;> assumption)
