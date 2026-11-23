import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqKerThetaOfDistinguishedAinf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_eq_ker_theta_of_distinguished_ainf : ∀ (l : ℕ) [Fact l.Prime] (x : Ainf l), Per.θ l x = 0 → IsUnit ((ainfDelta l).δ x) → Ideal.span {x} = RingHom.ker (Per.θ l) := by
  first | exact @GlobalTheory.BSP.span_eq_ker_theta_of_distinguished | exact GlobalTheory.BSP.span_eq_ker_theta_of_distinguished | (intros; apply GlobalTheory.BSP.span_eq_ker_theta_of_distinguished <;> assumption)
