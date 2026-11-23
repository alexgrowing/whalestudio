import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDoublingZetaValue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_doubling_zeta_value : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r₁ s₁ : ℕ),
    IsPair B M χX χW om r s r₁ s₁ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ (v : Pl F) (ρ : Fn F n d), (∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ) →
    ∀ (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)), IsSplitBasis t X.L b → UnrAt χW (splitPrime t) →
    ∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ (e : Fin n → ℤ) (T : GL (Fin n) (Fv F v)), T.1 = Matrix.diagonal (fun i => ϖ.1 ^ e i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n,
    ∀ g ∈ UAt σ X (evFin F v), GlobalTheory.KSplit.locMat t b g = k₁ * T * k₂ →
      coef m om (tens (evFin F v) (M.vac v) ρ) g =
        (chrW χW t ϖ : ℂ) ^ (∑ j, e j) * (((qV F v : ℝ) ^ (-((d : ℝ) / 2) * ((∑ j, |e j| : ℤ) : ℝ)) : ℝ) : ℂ) *
          coef m om (tens (evFin F v) (M.vac v) ρ) 1 := by
  first | exact @GlobalTheory.ThK.Bot.SplitCoef.coef_split | exact GlobalTheory.ThK.Bot.SplitCoef.coef_split | (intros; apply GlobalTheory.ThK.Bot.SplitCoef.coef_split <;> assumption)
