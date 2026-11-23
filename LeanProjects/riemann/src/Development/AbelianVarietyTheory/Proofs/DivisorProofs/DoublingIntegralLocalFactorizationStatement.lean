import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegralLocalFactorization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_integral_local_factorization : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ≠ 0 →
    ∀ v : Pl F, (¬ ∃ w, Formalism.UG.IsInertAt F E v w) → (∀ w ∈ aboveF (L := E) F v, UnrAt χW w) → φ v = M.vac v →
    ∀ μ : Measure (UAtSub σ X (evFin F v)), μ.IsHaarMeasure → μ {g | g.1 ∈ K} = 1 → ∀ s : ℂ, (n : ℝ) / 2 < s.re →
      zetaOn m om (pure f φ) i K₂ _ μ s = (∏ j ∈ Finset.range n, Lv (charFam χW) v (s + (n : ℂ) / 2 - (j : ℂ))) * denInv E n v s := by
  first | exact @GlobalTheory.ThK.Bot.SplitVal.zetaOn_split | exact GlobalTheory.ThK.Bot.SplitVal.zetaOn_split | (intros; apply GlobalTheory.ThK.Bot.SplitVal.zetaOn_split <;> assumption)
