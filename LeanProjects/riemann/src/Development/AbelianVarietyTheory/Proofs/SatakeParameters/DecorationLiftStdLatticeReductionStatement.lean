import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecorationLiftStdLatticeReduction
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoration_lift_std_lattice_reduction : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet E n ST SG) (w : SG), (∀ x, d.1.liftFr w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) ∧ ∀ x ∈ stdAt E n w.1, d.1.be w (d.1.liftFr w x) = redV w.1 x := by
  first | exact @GlobalTheory.decoSet_liftFr_lifts_level | exact GlobalTheory.decoSet_liftFr_lifts_level | (intros; apply GlobalTheory.decoSet_liftFr_lifts_level <;> assumption)
