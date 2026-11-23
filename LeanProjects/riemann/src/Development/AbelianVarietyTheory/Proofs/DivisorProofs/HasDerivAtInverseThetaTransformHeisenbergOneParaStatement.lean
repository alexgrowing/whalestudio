import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOnePara
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ (f f' : VA F N → ℂ) (C : ℝ), Continuous f → Continuous f' → (∀ w, ‖f w‖ ≤ C) → (∀ w, ‖f' w‖ ≤ C) → ∀ M : ℝ →+ VA F N, Continuous M → (∀ w s, HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (heisV ψ (M s) f' w) s) → ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0 := by
  first | exact @GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV | exact GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV | (intros; apply GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV <;> assumption)
