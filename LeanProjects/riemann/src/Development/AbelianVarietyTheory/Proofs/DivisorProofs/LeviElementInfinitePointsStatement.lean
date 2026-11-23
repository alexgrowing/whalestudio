import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementInfinitePoints
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
theorem _root_.GlobalTheory.T.levi_element_infinite_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ a ∈ idelesInf F E, toGAd hσ W.J hc (leviElt σ W W₁ H' a) ∈ infPts σ (c • W.J.map σ) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w), ∃ z : ℂ, z ≠ 0 ∧ GlobalTheory.Orb.archMat σ (c • W.J.map σ) τ (projArch σ (c • W.J.map σ) w (toGAd hσ W.J hc (leviElt σ W W₁ H' a))) = torMat ((c • W.J.map σ).map τ.1) (fun i => τ.1 (H'.x i)) (fun i => τ.1 (c⁻¹ * H'.y i)) z := by
  first | exact @GlobalTheory.LeviArch.leviElt_arch | exact GlobalTheory.LeviArch.leviElt_arch | (intros; apply GlobalTheory.LeviArch.leviElt_arch <;> assumption)
