import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jets_torsion_translates_cm_theta_product : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d r : ℕ) (b : Fin r → Matrix (Fin d) (Fin a) D.host.E), OnB D b → LocBasis D p (YYl D (stdL D a) (stdL D d)) b → ∀ (s : VC D a d) (Nn : ℕ), 0 < Nn → Nn • s ∈ LaB D (tor0 D cc δ) b → (p ∣ Nn → SplitIn D p) → ∀ (n : ℕ) (y : Fin n → Matrix (Fin d) (Fin a) D.host.E), (∀ i, y i ∈ YYl D (stdL D a) (stdL D d)) → iteratedFDeriv ℂ n (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0))) 0 (fun i => embV D (tor0 D cc δ) (y i)) ∈ Qbar ∧ ‖lamC lam (iteratedFDeriv ℂ n (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0))) 0 (fun i => embV D (tor0 D cc δ) (y i)))‖ ≤ (‖(Nn : ℂ_[p])‖⁻¹) ^ n * (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
  first | exact @GlobalTheory.ProductJets.jets_translate_product | exact GlobalTheory.ProductJets.jets_translate_product | (intros; apply GlobalTheory.ProductJets.jets_translate_product <;> assumption)
