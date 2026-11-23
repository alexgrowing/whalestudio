import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarCoeffEisensteinSeriesReversePoly
import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_coeff_eisenstein_series_reverse_poly : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O → ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x, star ((Formalism.L2.NT.eSerO O r f).coeff x) = (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := by
  first | exact @GlobalTheory.SerConj.star_coeff_eSerO | exact GlobalTheory.SerConj.star_coeff_eSerO | (intros; apply GlobalTheory.SerConj.star_coeff_eSerO <;> assumption)
