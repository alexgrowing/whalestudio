import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbDefs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbFin

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

theorem finSt : FinSt := by
  intro E _ _ _ B K₁ K₂ o₁ c₁ o₂ c₂ cK ψ₀ hc hψ
  exact ⟨fun A f hf => ⟨convF_idem B K₁ K₂ o₁ o₂ cK hc ψ₀ hψ f hf,
    fun ψ hψ' => convF_mulF_idem B K₁ K₂ o₁ c₁ o₂ c₂ cK hc ψ₀ hψ ψ hψ' f hf⟩,
    fun ψ _ => mulF_idem_rinv B K₁ K₂ cK ψ₀ hψ ψ⟩

end PositivityTheory.Rg.BcB.F.Rd.B

end
