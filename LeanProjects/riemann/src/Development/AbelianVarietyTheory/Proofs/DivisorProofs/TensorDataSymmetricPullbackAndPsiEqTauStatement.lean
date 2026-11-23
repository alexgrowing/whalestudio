import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataSymmetricPullbackAndPsiEqTau
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceFormTwistIso_of_matAct_of_latAct : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A₀ : Matrix (Fin r) (Fin r) ℤ) (O : Type) [CommRing O] [StarRing O] [Module O D'.toPre.X] (o : D'.toPre.OAct O) (w₀ : O), o.onB.act w₀ = GlobalTheory.TensAct.matAct T A₀ → (∀ y : D'.toPre.X, w₀ • y = GlobalTheory.TensAct.latAct T A₀ y) → W = (W + W.transpose) * A₀ → TraceFormTwistIso D'.toPre o w₀ := by
  first | exact @GlobalTheory.TensPsi.tensorData_symmetric_pullback_and_psi_eq_tau | exact GlobalTheory.TensPsi.tensorData_symmetric_pullback_and_psi_eq_tau | (intros; apply GlobalTheory.TensPsi.tensorData_symmetric_pullback_and_psi_eq_tau <;> assumption)
