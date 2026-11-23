import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftHaarIntegralConvergent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_haar_integral_convergent : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
    coef m om (pure f φ) 1 ≠ 0 → ∀ (T : Finset (Pl F)) (g : UA σ X.J), (∀ v ∉ T, compAt σ X.J v g = 1) →
      coef m om (pure f φ) g / coef m om (pure f φ) 1 = coef m om (pure f φ) (compArch σ X.J g) / coef m om (pure f φ) 1 *
        ∏ v ∈ T, coef m om (pure f φ) (compAt σ X.J v g) / coef m om (pure f φ) 1 := by
  first | exact @GlobalTheory.ThK.Bot.CoefFin.coef_div_eq_prod | exact GlobalTheory.ThK.Bot.CoefFin.coef_div_eq_prod | (intros; apply GlobalTheory.ThK.Bot.CoefFin.coef_div_eq_prod <;> assumption)
