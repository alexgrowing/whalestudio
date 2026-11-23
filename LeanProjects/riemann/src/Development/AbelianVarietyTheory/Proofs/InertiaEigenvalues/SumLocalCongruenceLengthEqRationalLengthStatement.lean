import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLength
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ZRat D (D.what₂.muTw w) j → (∀ i ∈ D.nd.locs j w, SpecPr D i) → D.what₂.etaJ j w = etaRat D (D.what₂.muTw w) j w := by
  first | exact @GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat | exact GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat | (intros; apply GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat <;> assumption)
