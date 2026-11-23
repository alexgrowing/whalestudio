import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

def SiegelEisensteinDoubled : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ (B : Base F E) (n : ℕ), 1 ≤ n →
  ∀ W : Spc F E n, (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
  ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
  ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
  ∀ χ : Chr F E, IsHecke F E χ →
  ∀ (s₁ : ℂ) (φ : UA σ W₂.J → ℂ), φ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χ s₁ →
    let P : Subgroup (UA σ W₂.J) := siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype
    let f : ℂ → UA σ W₂.J → ℂ := flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ s₁
    ∃ Ei : ℂ → UA σ W₂.J → ℂ,
      (∀ s : ℂ, (n : ℝ) / 2 < s.re → ∀ g,
        Eis.CosetConv P (ratU σ W₂.J) (f s) g ∧ Ei s g = Eis.cosetSum P (ratU σ W₂.J) (f s) g) ∧
      ∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → UA σ W₂.J → ℂ), 0 < r ∧
        (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Ei s g) ∧
        (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₀ r)) ∧
        ContinuousOn (fun x : ℂ × UA σ W₂.J => H x.1 x.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
        ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N

end GlobalTheory.Published

end
