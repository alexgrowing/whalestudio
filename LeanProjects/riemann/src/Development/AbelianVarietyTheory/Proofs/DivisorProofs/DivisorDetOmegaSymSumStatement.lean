import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDetOmegaSymSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_det_omega_sym_sum : ∀ (D : D7) (O : Setup D) (c : O.s.Comp), (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).D = ∑ k : Fin (D.R.f * O.N), (-1 : ℤ) • (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).D := by
  first | exact @GlobalTheory.DetOm.div_adl_detOmegaSym | exact GlobalTheory.DetOm.div_adl_detOmegaSym | (intros; apply GlobalTheory.DetOm.div_adl_detOmegaSym <;> assumption)
