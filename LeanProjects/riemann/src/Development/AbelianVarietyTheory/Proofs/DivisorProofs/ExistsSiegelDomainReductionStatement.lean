import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_domain_reduction : GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y ∧ ∃ (Cc : Set (UA σ X.J)) (c C : ℝ) (A : ℕ),
      IsCompact Cc ∧ 0 < c ∧ ∀ g : UA σ X.J, ∃ γ ∈ ratU σ X.J, ∃ (t : Fin q → ℝ) (a κ : UA σ X.J),
        (∀ i, c ≤ t i) ∧ IsTorusU x y t a ∧ κ ∈ Cc ∧ γ * g = a * κ ∧ (ht (a * κ) : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  first | exact @GlobalTheory.SiegelHt.siegel_reduction | exact GlobalTheory.SiegelHt.siegel_reduction | (intros; apply GlobalTheory.SiegelHt.siegel_reduction <;> assumption)
