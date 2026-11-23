import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesInjectiveLocalRing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_injective_localRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ f, taylor ev (fun i => ⇑(ds i)) f = 0 → f = 0 := by
  first | exact @GlobalTheory.TaylorInj.taylor_injective | exact GlobalTheory.TaylorInj.taylor_injective | (intros; apply GlobalTheory.TaylorInj.taylor_injective <;> assumption)
