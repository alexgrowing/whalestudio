import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFinitenessStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltrationStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

theorem suppExists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SuppExists k := by
  intro N V _ _ π hs hi
  have hG : GlobalTheory.Published.GeometricLemma := GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration GlobalTheory.T.bernstein_zelevinsky_finiteness PositivityTheory.Geo.geometricLemmaFiltration
  obtain ⟨s, h⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport GlobalTheory.T.bernstein_zelevinsky_finiteness hG (IrrGL.of π hs hi)
  exact ⟨s, h.of_equiv (IrrGL.equivOf π hs hi).symm⟩

theorem genericUnlinkedGL_of
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      SuppExists k)
    (hU : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      GenericUnique k)
    (hR : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      UnlinkedRealize k) :
    GlobalTheory.Published.GenericUnlinkedGL := by
  intro k _ _ _ _ _ N V _ _ π hs hi hg
  obtain ⟨s, hsupp⟩ := hS k N V π hs hi
  have hsum : (s.map Sigma.fst).sum = N := by simpa using hsupp.sum_fst
  obtain ⟨h, Δ, x, hd, hΔ, hL, hx, hxg⟩ := hR k N s (fun y hy => hsupp.isCusp hy) hsum
  exact ⟨h, Δ, x, hd, hΔ, hL, hU k N s V _ π (prodIrr x hd) hsupp hx hg hxg⟩

end GlobalTheory.RgGu

end
