import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.SphLocProd

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail

theorem sphMono : SphMono := by
  intro E _ _ _ n D w K K' hle h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  exact (Submodule.ne_bot_iff _).2
    ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hv k (hle hk), hv0⟩

theorem satSph : SatSph := by
  intro E _ _ _ n D w B hB
  obtain ⟨b, hb, -⟩ := hB
  exact GlobalTheory.Rigid.isSpherical_locProd D.h w (D.σ · w) fun i => (hb i).1

end PositivityTheory.Rg.BcB.F.Tail

end
