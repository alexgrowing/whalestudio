import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegIdentitySymm
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullDeg_identity_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), IsPullDeg (RingHom.id R) D D' → Nonempty (IsPullDeg (RingHom.id R) D' D) := by
  first | exact @GlobalTheory.PullDegSymm.isPullDeg_symm | exact GlobalTheory.PullDegSymm.isPullDeg_symm | (intros; apply GlobalTheory.PullDegSymm.isPullDeg_symm <;> assumption)
