import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingSeesawIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_seesaw_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ Φ ∈ PolData B M, Φ ≠ 0 → M.I om Φ = 0 → ∀ μ : Measure (⊤ : Subgroup (UA σ X.J)), μ.IsHaarMeasure →
      GlobalTheory.Cont.HolValueAt (zetaOn m om Φ i K₂ ⊤ μ) (((d : ℂ) - (n : ℂ)) / 2) 0 := by
  first | exact @GlobalTheory.ThK.Bot.NormZero.holValueAt_zero | exact GlobalTheory.ThK.Bot.NormZero.holValueAt_zero | (intros; apply GlobalTheory.ThK.Bot.NormZero.holValueAt_zero <;> assumption)
