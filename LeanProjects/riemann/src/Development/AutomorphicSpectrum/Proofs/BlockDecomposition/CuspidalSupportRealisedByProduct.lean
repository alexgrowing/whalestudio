import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocksStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenSupp

theorem hasSupport_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL k)), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  intro k _ _ _ _ N V _ _ π s hπ
  obtain ⟨h, x, hs, -, hc, e, hsq⟩ := hπ
  have hd : ∑ a, (x a).1 = N := by
    have := Fintype.card_congr e
    simpa [Fintype.card_sigma] using this
  obtain ⟨φ⟩ := GlobalTheory.T.multiProd_equiv_standard_blocks k (fun a => (x a).1) hd e _ (fun a => (x a).rep)
  exact ⟨h, x, hd, hs, fun a => ⟨(hc a).1, (hc a).2.2⟩, hsq.trans (GlobalTheory.JacStages.isSubquotient_of_equiv φ)⟩

end GlobalTheory.CompanionTheory.GenSupp
