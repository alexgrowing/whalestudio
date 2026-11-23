import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr

noncomputable section

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published

namespace GlobalTheory.LocGL

theorem hasSupport_msupp_of_isL (hZ : ZelevinskyPolynomialRing) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL k)
    (h : IsL 𝔪 x.rep) : HasSupport x.rep (msupp 𝔪) := by

  obtain ⟨_, Ψ, -, hΨ, -⟩ := hZ k

  obtain ⟨c, y, hd, ⟨Δ, ⟨hΔ, -⟩, hy⟩, hx⟩ := h

  have key : HasSupport x.rep (∑ a, (Δ a).ms) :=
    SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ (fun a => (hy a).hasSupport) hx.1 hx.isSubquotient

  have e : msupp 𝔪 = ∑ a, (Δ a).ms := by
    rw [← hΔ, msupp, Multiset.bind, Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  rw [e]
  exact key

end GlobalTheory.LocGL
