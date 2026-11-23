import Mathlib
import Formalism.LocalToGlobal.Columns.LevGSym
import Formalism.LocalToGlobal.HermitianForms.DefsSym
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
import Formalism.LocalToGlobal.Columns.RecLevelSymF
open Formalism.L2.Col

namespace GlobalTheory

theorem mem_HJsym_iff_JSymG : ∀ (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n), r = k + 2 * rS + 1 → 0 < t → n = r + m * t →
    ∀ M : GL (Fin n) κ, M ∈ HJsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t false := by
  intro κ _ n k r t m rS h hr ht hn M
  subst hr
  rw [HJsym_eq_JSymG ht (by omega) h]

end GlobalTheory
