import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumDatumNumbersEqHostOfCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numDatum_numbers_eq_host_of_compatible : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X), HostTie N s Pr → N.rd = D.host.rdE ∧ N.v = D.host.v ∧ N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D ∧ N.logOm = TaylorLogMetric.logOmVal D ∧ TaylorLogMetric.fF D = N.R.f ∧ X.f = N.R.f ∧ Module.finrank ℚ X.E = 2 * N.R.f ∧ |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd ∧ TaylorLogMetric.IsCurveIdeal D D.host.ccK := by
  first | exact @GlobalTheory.ColNorms.numbers_of_hostTie | exact GlobalTheory.ColNorms.numbers_of_hostTie | (intros; apply GlobalTheory.ColNorms.numbers_of_hostTie <;> assumption)
