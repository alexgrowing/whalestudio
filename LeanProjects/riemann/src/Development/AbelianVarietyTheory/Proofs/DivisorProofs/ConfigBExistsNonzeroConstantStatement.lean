import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBExistsNonzeroConstant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_exists_nonzero_constant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ ∈ PolData B G.M, ∀ h, IntegrableOn (fun g => thetaSum F (e (om (g, h) Φ))) G.M.dom G.M.μ ∧ ∫ g in G.M.dom, thetaSum F (e (om (g, h) Φ)) ∂G.M.μ = κ * G₁.M.I om₁ (e (om (1, h) Φ)) 1 := by
  first | exact @GlobalTheory.ThKFirstV.firstV | exact GlobalTheory.ThKFirstV.firstV | (intros; apply GlobalTheory.ThKFirstV.firstV <;> assumption)
