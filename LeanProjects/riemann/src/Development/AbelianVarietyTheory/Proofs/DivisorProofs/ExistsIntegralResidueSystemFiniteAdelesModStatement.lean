import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralResidueSystemFiniteAdelesMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_residue_system_finiteAdeles_mod : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∃ R : Finset (Af E), (∀ a ∈ R, ∀ w, Valued.v (a w) ≤ 1) ∧ ∀ z : Af E, (∀ w, Valued.v (z w) ≤ 1) → ∃! a, a ∈ R ∧ ∀ w, Valued.v (z w - a w) ≤ radN E N w := by
  first | exact @GlobalTheory.CMVal.LatEnt.Res.exists_residues | exact GlobalTheory.CMVal.LatEnt.Res.exists_residues | (intros; apply GlobalTheory.CMVal.LatEnt.Res.exists_residues <;> assumption)
