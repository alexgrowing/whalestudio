import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDoublingIntegralUnramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_doubling_integral_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r₁ s₁ : ℕ),
    IsPair B M χX χW om r s r₁ s₁ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ (v : Pl F) (ρ : Fn F n d), (∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ) →
    ∀ (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) ι, M.IsLinW B.ψ t b c ι →
    ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v), (∀ Y, ι φ₁ Y * ι φ₂ Y = 0) →
      ∫ x, tens (evFin F v) φ₁ ρ x * starRingEnd ℂ (tens (evFin F v) φ₂ ρ x) ∂m = 0 := by
  first | exact @GlobalTheory.DisjOrth.disj_orth | exact GlobalTheory.DisjOrth.disj_orth | (intros; apply GlobalTheory.DisjOrth.disj_orth <;> assumption)
