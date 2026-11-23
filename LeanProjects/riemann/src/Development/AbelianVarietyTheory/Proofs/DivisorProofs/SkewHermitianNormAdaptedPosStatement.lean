import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNormAdaptedPos
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_norm_adapted_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ τ : E →+* ℂ, (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (H'.x i)) = 0 ∧ (star (fun i => τ (c⁻¹ * H'.y i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 0 ∧ (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 1 := by
  first | exact @GlobalTheory.TorFinArch.isotropic_dual_plane | exact GlobalTheory.TorFinArch.isotropic_dual_plane | (intros; apply GlobalTheory.TorFinArch.isotropic_dual_plane <;> assumption)
