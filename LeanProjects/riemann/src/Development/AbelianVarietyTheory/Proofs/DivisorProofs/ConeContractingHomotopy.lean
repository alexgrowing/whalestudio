import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitSectionAvoid
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_contracting_homotopy : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ), (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b), ε a b (bop α β) = 1) ∧ (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧ ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)), cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  first | (exact @GlobalTheory.EZ.Cone.coneContraction) | (exact GlobalTheory.EZ.Cone.coneContraction) | (intros; apply GlobalTheory.EZ.Cone.coneContraction  <;> assumption)
