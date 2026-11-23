import Mathlib
import Formalism.PeriodIntegrals.TransferenceCoverRad
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover

open scoped InnerProductSpace

noncomputable section

namespace PI.Tr2

theorem coverDiv : PI.TransferenceCoverDiv := by
  intro V _ _ _ M hd hspan κ hκ hdual x
  haveI := hd
  haveI : IsZLattice ℝ M := ⟨hspan⟩
  obtain ⟨l, hl, hle⟩ := transference_covering V M κ hκ (fun y hy0 hy => hdual y hy hy0) x
  refine ⟨l, hl, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  linarith

end PI.Tr2
