import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleFrameMembership
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subbundle_frame_membership : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (S : ∀ x : X, Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) (l : ℕ), (∀ (y : X) (hy : y ∈ U), S y = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)}) → ∀ {V : X.Opens} (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ (VB.Sub.ofStalks S).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 := by
  first | exact @GlobalTheory.VB.sum_smul_frame_mem_ofStalks_iff | exact GlobalTheory.VB.sum_smul_frame_mem_ofStalks_iff | (intros; apply GlobalTheory.VB.sum_smul_frame_mem_ofStalks_iff <;> assumption)
