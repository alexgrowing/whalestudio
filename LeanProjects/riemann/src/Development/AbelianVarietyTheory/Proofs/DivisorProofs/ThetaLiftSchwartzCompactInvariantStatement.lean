import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSchwartzCompactInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_schwartz_compact_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ K : Subgroup (UA σ X.J), IsCompact {k : UA σ X.J | compArch σ X.J k = 1 ∧ ∀ v, compAt σ X.J v k ∈ K} →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ S₀ : Finset (Pl F), ∀ k : UA σ X.J, compArch σ X.J k = 1 → (∀ v, compAt σ X.J v k ∈ K) →
      (∀ v ∈ S₀, compAt σ X.J v k = 1) → om (k, 1) Φ = Φ := by
  first | exact @GlobalTheory.ThK.BotFixFin.fix_off_finset | exact GlobalTheory.ThK.BotFixFin.fix_off_finset | (intros; apply GlobalTheory.ThK.BotFixFin.fix_off_finset <;> assumption)
