import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleFrameExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_bundle_frame_exists : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (P : VB.Sub F) (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (l : ℕ), l ≤ N → (∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) → ∃ e : Fin (N - l) → Γ(cokernel P.incl, U), VB.IsFrame e := by
  first | exact @GlobalTheory.VB.exists_isFrame_cokernel_of_frame | exact GlobalTheory.VB.exists_isFrame_cokernel_of_frame | (intros; apply GlobalTheory.VB.exists_isFrame_cokernel_of_frame <;> assumption)
