import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqNegOnePow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleConstant_eq_neg_one_pow : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∀ (P : Ideal (𝓞 D.host.E)) (r : ℕ), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → (∃ a, a - sgO D a ∉ P) → TriDat D T A₁ A₂ A₃ P r → μ = (-1) ^ r := by
  first | exact @GlobalTheory.TriangleSign.mu_eq_sign | exact GlobalTheory.TriangleSign.mu_eq_sign | (intros; apply GlobalTheory.TriangleSign.mu_eq_sign <;> assumption)
