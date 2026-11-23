import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingLFunctionSpecialValue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_l_function_special_value : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (k : InfinitePlace F → ℤ), HasExp B.emb χW k → (∀ w, (d : ℤ) < |k w|) → ∀ T : Finset (Pl F), T ⊆ B.P → UnrOff χW (T : Set (Pl F)) →
    (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χW w) →
    (∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
      ∃ f ∈ M.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ≠ 0 →
        ∀ μ : Measure (UAtSub σ X (evI F)), μ.IsHaarMeasure → ∃ z : ℂ, z ≠ 0 ∧ ∀ s : ℂ, zetaOn m om (pure f φ) i K₂ _ μ s = z) →
    ∃ Φ ∈ PolData B M, M.I om Φ ≠ 0 := by
  first | exact @GlobalTheory.ThK.Bot.Asm.exists_polData_I_ne_zero | exact GlobalTheory.ThK.Bot.Asm.exists_polData_I_ne_zero | (intros; apply GlobalTheory.ThK.Bot.Asm.exists_polData_I_ne_zero <;> assumption)
