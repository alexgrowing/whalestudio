import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledLeftInvariantContinuous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_left_invariant_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → IsCMExt F E σ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ Φ : UA σ W₂.J → ℂ, Continuous Φ →
    GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) Φ →
    (∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype,
      aOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype p = 1 → ∀ g, Φ (p * g) = Φ g) →
    ∀ w : UA σ W.J → ℂ, Continuous w → (∀ x y, w (x * y) = w x * w y) → (∀ γ ∈ ratU σ W.J, w γ = 1) →
    (∀ x : UA σ W.J, Matrix.GeneralLinearGroup.det x.1 = 1 → w x = 1) →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) → GlobalTheory.ThKLiftCusp.IsCuspW W f →
    ∀ γ ∈ ratU σ W₂.J, (¬ ∃ δ ∈ ratU σ W.J, γ * (i (1, δ))⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) →
    ∀ S : Subgroup (UA σ W.J),
      (∀ g, g ∈ S ↔ g ∈ ratU σ W.J ∧ γ * i (1, g) * γ⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) →
    ∀ (h : UA σ W.J) (D : Set (UA σ W.J)), IsFundamentalDomain S D μ →
      IntegrableOn (fun x => f x * (Φ (γ * i (h, x)) * w x)) D μ →
      ∫ x in D, f x * (Φ (γ * i (h, x)) * w x) ∂μ = 0 := by
  first | exact @GlobalTheory.OrbitVanish.integral_eq_zero | exact GlobalTheory.OrbitVanish.integral_eq_zero | (intros; apply GlobalTheory.OrbitVanish.integral_eq_zero <;> assumption)
