import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge

theorem finCohSt_of_cmpSt : CmpSt → FinCohSt := by
  intro h R _ _ X s _ P _ _ S
  letI := GlobalTheory.algebraΓOfHom s
  have hf : ∀ p, Module.Finite R (GlobalTheory.coh (GlobalTheory.structureModule X) p) := fun p ↦
    GlobalTheory.ProperFinite.finite_coh_of_isProper s (GlobalTheory.structureModule X) p
  obtain ⟨⟨e₀⟩, hn⟩ := h R X s inferInstance P S
  refine ⟨?_, fun n ↦ ?_⟩
  · have := hf 0
    exact Module.Finite.equiv e₀.symm
  · obtain ⟨e⟩ := hn n
    have := hf (n + 1)
    exact Module.Finite.equiv e.symm

end GlobalTheory.CompanionTheory.Hodge
