import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotients
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotientAltBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProductStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversed_product_same_subquotients : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  first | exact @GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | exact GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | (intros; apply GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev <;> assumption)
