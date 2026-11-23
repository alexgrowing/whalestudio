import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ProdFlattenDep

open GlobalTheory.ProdFlatten

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in

theorem of_iso {d c M : ℕ} (len : Fin d → ℕ) (y : ∀ i, Fin (len i) → IrrGL k) (N : Fin d → ℕ)
    (hN : ∀ i, ∑ j, (y i j).1 = N i) (hM : ∑ i, N i = M) (z : Fin c → IrrGL k) (hz : ∑ p, (z p).1 = M)
    (H : Iso (mp N hM fun i => pr (y i) (hN i)) (pr z hz)) :
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv (prodIrr z hz)) := H

end GlobalTheory.CompanionTheory.ProdFlattenDep
