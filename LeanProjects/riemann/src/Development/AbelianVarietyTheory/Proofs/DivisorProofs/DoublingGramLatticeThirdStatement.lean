import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingGramLatticeThird
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
theorem _root_.GlobalTheory.T.doubling_gram_lattice_third : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → 1 ≤ d →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χX (((n : ℂ) - (d : ℂ)) / 2),
    (∀ s : ℂ, (d : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g) →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∀ s : ℂ, (d : ℝ) / 2 < s.re → ∀ 𝓕 : Set (UA σ W.J), IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
      ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → GlobalTheory.ThKLiftCusp.IsCuspW W f → ∀ h, ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖GlobalTheory.Eis.term (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, x)) q‖ₑ ∂μ ≠ ⊤ →
      ∫ x in 𝓕, f x * (∑' q : {q : GlobalTheory.Eis.Cosets (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) // ¬ ∃ δ ∈ ratU σ W.J,
        ((q.out : ratU σ W₂.J) : UA σ W₂.J) * (i (1, δ))⁻¹ ∈ (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype)},
        GlobalTheory.Eis.term (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, x)) q.1) * (((χX (Matrix.GeneralLinearGroup.det x.1))⁻¹ : Circle) : ℂ) ∂μ = 0 := by
  first | exact @GlobalTheory.DoublingNonOpen.nonOpen_vanish | exact GlobalTheory.DoublingNonOpen.nonOpen_vanish | (intros; apply GlobalTheory.DoublingNonOpen.nonOpen_vanish <;> assumption)
