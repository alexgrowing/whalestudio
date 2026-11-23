import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegralUnfolding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_integral_unfolding : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ≠ 0 →
    ∀ (μ : Measure (⊤ : Subgroup (UA σ X.J))) (μi : Measure (UAtSub σ X (evI F))) (μv : ∀ v : Pl F, Measure (UAtSub σ X (evFin F v))),
      μ.IsHaarMeasure → μi.IsHaarMeasure → (∀ v, (μv v).IsHaarMeasure ∧ μv v {g | g.1 ∈ K} = 1) →
      ∃ (c : ℂ) (R : ℝ), c ≠ 0 ∧ ∀ s : ℂ, R < s.re → ∃ P : ℂ, HasProd (fun v : Pl F => zetaOn m om (pure f φ) i K₂ _ (μv v) s) P ∧
        zetaOn m om (pure f φ) i K₂ ⊤ μ s = c * zetaOn m om (pure f φ) i K₂ _ μi s * P := by
  first | exact @GlobalTheory.ThK.Bot.Euler.zeta_euler | exact GlobalTheory.ThK.Bot.Euler.zeta_euler | (intros; apply GlobalTheory.ThK.Bot.Euler.zeta_euler <;> assumption)
