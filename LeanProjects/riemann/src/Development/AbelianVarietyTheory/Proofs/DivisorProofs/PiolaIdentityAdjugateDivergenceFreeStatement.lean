import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiolaIdentityAdjugateDivergenceFree
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piola_identity_adjugate_divergence_free : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R) (M : Matrix ι ι R), (∀ h i j, δ h (M i j) = δ i (M h j)) → ∀ j, ∑ i, δ i (M.adjugate j i) = 0 := by
  first | exact @GlobalTheory.PiolaAlg.piola_identity | exact GlobalTheory.PiolaAlg.piola_identity | (intros; apply GlobalTheory.PiolaAlg.piola_identity <;> assumption)
