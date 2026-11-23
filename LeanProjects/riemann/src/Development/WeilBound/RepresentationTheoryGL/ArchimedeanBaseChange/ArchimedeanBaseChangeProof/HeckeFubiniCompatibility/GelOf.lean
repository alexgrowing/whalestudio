import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousOnFtA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousOnFtB

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

theorem gelOf (hW : WaveEx) (hF : CompatFub) (hTT : TensTest) : GelOf := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _ ν _ Ma Mb κ _ ka kb va vb T ψ f c c' v g s m hC hka hkb hψ hg _ hf hc hrep
  refine ⟨fun k' hk0 hk' hrep' i y m₂ x hx => ?_, fun k' hk0 hk' hrep' i y m₁ x hx => ?_⟩
  · exact Slice.gelA hW hF hTT D hC v hka hkb hψ hg hf hc hrep k' hk0 hk' hrep' i y m₂ hx
  · exact Slice.gelB hW hF hTT D hC v hka hkb hψ hg hf hc hrep k' hk0 hk' hrep' i m₁ y hx

end PositivityTheory.Rg.BcB.CG

end
