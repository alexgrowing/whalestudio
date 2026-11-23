import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hInv_of_directed_union_subalgebras : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (S : ι → Subalgebra ℤ A), Monotone S → (∀ a, ∃ i, a ∈ S i) → (∀ i, IsUnit (q : S i)) → (∀ i, HInv q (S i)) → HInv q A := by
  first | (exact @GlobalTheory.EtC.hInv_of_directed_union) | (exact GlobalTheory.EtC.hInv_of_directed_union) | (intros; apply GlobalTheory.EtC.hInv_of_directed_union  <;> assumption)
