import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableOfCharOne
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleApply
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZAux
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open Classical

noncomputable section

namespace GlobalTheory.LocGL.ZelevinskyExpansion

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem msupp_eq_of_isL {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    (hπ : π.IsIrreducible) {𝔫 : Multiset (Segment k)} (h𝔫 : IsL 𝔫 π) {s : Multiset (IrrGL k)}
    (hs : HasSupport π s) : msupp 𝔫 = s := by
  obtain ⟨h, y, hd, ⟨D, ⟨hD, -⟩, hz⟩, hcos⟩ := h𝔫
  have hsy : HasSupport π (∑ i, (D i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hz i).hasSupport) hπ hcos.isSubquotient
  have heq := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique CompanionTheory.Exh.geometricLemmaGL
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hsy hs
  rw [← heq, msupp, ← hD, Multiset.bind_map]
  rfl

end GlobalTheory.LocGL.ZelevinskyExpansion
