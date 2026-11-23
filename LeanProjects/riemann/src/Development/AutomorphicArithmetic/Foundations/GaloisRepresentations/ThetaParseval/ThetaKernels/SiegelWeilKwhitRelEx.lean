import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitRelAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictAssemble
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentParamRationalMatrix

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem relEx_of_k (hA : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelAlg_k) (hS : SdEx) (hR : _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.RelRealP_k) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelEx_k := by
  intro _ _ F E _ _ _ _ _ σ d R Φ _ P gf hP x t u hx T hTnd
  obtain ⟨η, hOf, hη, hherm, hof, haniso, hcm, hJ, hTT⟩ := hA F E σ d
  obtain ⟨T₀, hrat, hTdh, hTdd⟩ := hTT T hTnd
  obtain ⟨θ, fr, g, l, εs, Φg, Φf, Φv, hth, hfr, hg, hΦg, hεs, hchr, hpl, hfrm, hpf, hpr⟩ :=
    hR F E σ d R Φ P gf hP x t u hx η hη hherm
  obtain ⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩ := hS F E σ hcm d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) hJ d.B.ψ hchr d.n
  exact ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, ⟨hx, hrat, hη, hherm, hof, hth, hfr, hg⟩, hΦg, haniso, hεs,
    hcm, hJ, hTdh, hTdd, hchr, hpl, hfrm, hpf, hpr, hμ, hν⟩
theorem relEx_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelEx_k := _root_.PositivityTheory.SiegelWeilFormula.KWhit.relEx_of_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.relAlg_pf_k sdEx _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.relReal_k
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
