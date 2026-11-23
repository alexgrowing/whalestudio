import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtSpecProdSelfOfBasicOpenPreimageEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O → h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) → h = h' := by
  first | exact @GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | exact GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | (intros; apply GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen <;> assumption)
