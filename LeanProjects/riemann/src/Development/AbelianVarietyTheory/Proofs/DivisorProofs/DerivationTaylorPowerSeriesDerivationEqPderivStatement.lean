import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv B a (taylor ev (fun i => ⇑(ds i)) f) := by
  first | exact @GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | exact GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | (intros; apply GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv <;> assumption)
