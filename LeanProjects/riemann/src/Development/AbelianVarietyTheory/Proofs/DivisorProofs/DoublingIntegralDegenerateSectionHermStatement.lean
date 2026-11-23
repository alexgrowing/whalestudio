import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegralDegenerateSectionHerm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_integral_degenerate_section_herm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' → min r s' = 0 →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ (χ : Chr F E) (s₀ : ℂ) (σ₀ : ℝ), ∀ f ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ χ s₀,
    (∀ s : ℂ, σ₀ < s.re →
      GlobalTheory.AutomorphicL2Unitary.LeftInv (siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype ⊓ ratU σ X₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ f s₀ s) ∧
      ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype) (ratU σ X₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ f s₀ s) g) →
    ∀ Ψ : UA σ X₂.J → ℂ, (∀ g, GlobalTheory.Cont.HolValueAt (fun s => GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype) (ratU σ X₂.J)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ f s₀ s) g) s₀ (Ψ g)) →
    ∀ (μ : Measure (UA σ X.J)) (𝓕 : Set (UA σ X.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) 𝓕 μ →
      GlobalTheory.Cont.HolValueAt (fun s => ∫ g, flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ f s₀ s (i (g, 1)) ∂μ) s₀
        (∫ g in 𝓕, Ψ (i (g, 1)) ∂μ) := by
  first | exact @GlobalTheory.ThK.Bot.UnfFirst.holValueAt_first | exact GlobalTheory.ThK.Bot.UnfFirst.holValueAt_first | (intros; apply GlobalTheory.ThK.Bot.UnfFirst.holValueAt_first <;> assumption)
