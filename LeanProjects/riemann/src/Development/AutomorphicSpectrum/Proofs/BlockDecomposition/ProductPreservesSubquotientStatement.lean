import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotient
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_preserves_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M) (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i)) (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i)), (∀ i, IsSmooth (ρ' i)) → (∀ i, IsSubquotient (ρ i) (ρ' i)) → IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') := by
  first | exact @GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | exact GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | (intros; apply GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall <;> assumption)
