import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSpecProdSelfPreimageEqClopen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U → ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧ ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  first | exact @GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen | exact GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen | (intros; apply GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen <;> assumption)
