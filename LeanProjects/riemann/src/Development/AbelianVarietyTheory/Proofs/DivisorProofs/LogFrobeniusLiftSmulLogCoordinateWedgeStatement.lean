import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedge
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge : ∀ (K : Type) [Field K] (p : ℕ) (n : ℕ) (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K), IsCartierMap p x γ → ∀ (c : K) (I : Finset (Fin n)), γ (c • logWedge x I) = c ^ p • logWedge x I := by
  first | exact @GlobalTheory.cartierMap_smul_logWedge | exact GlobalTheory.cartierMap_smul_logWedge | (intros; apply GlobalTheory.cartierMap_smul_logWedge <;> assumption)
