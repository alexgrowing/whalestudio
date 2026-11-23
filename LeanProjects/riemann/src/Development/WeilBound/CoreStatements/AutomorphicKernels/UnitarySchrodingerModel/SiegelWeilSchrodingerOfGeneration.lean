import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.SiegelWeilSchrodingerOfLocal
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top7

noncomputable section

namespace PositivityTheory.PfSWUS

open PositivityTheory.Rg.Sw.Glob

theorem siegel_weil_schrodinger_of_generation (hGA : GenA) (hId : GIdil) (hG : PositivityTheory.SiegelWeilFormula.Gen.WhitGenLt) :
    GlobalTheory.Published.SiegelWeilUnitarySchrodingerLit := by
  intro D n V a1 a2 a3 ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω H hH l hl s hs ν hν Φ hΦ g
  exact top7 hGA hId (coefND_of wtc hG) D n V ψ χ θ μ ω H l s ν Φ
    ⟨hψ, hχ, hη, hθ, ⟨𝓕, hμ⟩, hω, hH, hl, hs, hν, hΦ⟩ ⟨a1, a2, a3⟩ (by omega) g

end PositivityTheory.PfSWUS

end
