import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → (∀ j' : Per.Acris l →+* Per.BdRp l, IsCrisP j' → j' = j) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), j (sigA g x) = Per.σDp g (j x)) ∧ ∀ (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l), (∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧ Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) = Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) → Per.ev l n (j x) = Per.ev l n y := by
  first | exact @GlobalTheory.MemLoc.crisP_unique_equivariant | exact GlobalTheory.MemLoc.crisP_unique_equivariant | (intros; apply GlobalTheory.MemLoc.crisP_unique_equivariant <;> assumption)
