import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentRadicalFlagStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_flag_stabilizer : ∀ (k : Type) [Field k] (a s : ℕ) (d : Fin s → ℕ) (e : (Σ i, Fin (d i)) ≃ Fin a), GlobalTheory.SmGL.unipRad k e ≠ ⊥ → ∃ W : Submodule k (Fin a → k), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin a) k, (∀ v, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v ∈ W) → (∀ v ∈ W, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v = 0) → g ∈ GlobalTheory.SmGL.unipRad k e := by
  first | exact @GlobalTheory.UnipFlag.exists_sub | exact GlobalTheory.UnipFlag.exists_sub | (intros; apply GlobalTheory.UnipFlag.exists_sub; all_goals assumption)
