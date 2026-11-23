import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateNormalizedVectorIntegralCombTensorPower
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  first | exact @GlobalTheory.MomN.transl_normVec_int | exact GlobalTheory.MomN.transl_normVec_int | (intros; apply GlobalTheory.MomN.transl_normVec_int <;> assumption)
