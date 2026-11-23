import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRealPointsBijectiveMultiplicative
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_real_points_bijective_multiplicative : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), (∀ x : InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, (∀ w, Matrix.of (x w) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) → ∃ g : X.B.I.Ginf, Gm D (trX X C g) = x) ∧ Function.Injective (fun g : X.B.I.Ginf => Gm D (trX X C g)) ∧ ∀ (s g : X.B.I.Ginf) (w : InfinitePlace D.host.E), Matrix.of (Gm D (trX X C (s * g)) w) = Matrix.of (Gm D (trX X C s) w) * Matrix.of (Gm D (trX X C g) w) := by
  first | exact @GlobalTheory.CovDom.transport_real_points | exact GlobalTheory.CovDom.transport_real_points | (intros; apply GlobalTheory.CovDom.transport_real_points <;> assumption)
