import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KeepQ
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PeakAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RealAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.WordRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem peakRun : PeakRun := by
  intro E _ _ _ B Q _ χa χb Γ _ t arch a₀ x g ρ hG hK hT hHa hHb ha hv hψ hmul hadj hρ hs
  have hkeep : ∀ y, ∀ f ∈ Q, (t y).op f ∈ Q ∧ star (t y).op f ∈ Q := by
    intro y f hf
    have h1 := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t y) (t y) (hG.ok y) (hG.ok y)
    obtain ⟨hT1, hR1, -, -, hadjOk, hadjOp, -, -⟩ := h1
    have h2 := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t y).adj (t y).adj hadjOk hadjOk
    refine ⟨hK _ _ hT1 hR1 f hf, ?_⟩
    rw [ContinuousLinearMap.star_eq_adjoint, ← hadjOp]
    exact hK _ _ h2.1 h2.2.1 f hf
  obtain ⟨𝔄⟩ := algEx B.Hb Q Γ (fun y => (t y).op) (fun y => (t y).val χa χb) hG.comm hG.commStar hkeep
  obtain ⟨J, hJ, c, w, hval, hnorm⟩ := peakAlg B.Hb Q Γ (fun y => (t y).op) (fun y => (t y).val χa χb) 𝔄 arch a₀ x ρ ha hv hρ
    (fun s hb hsa => hs (fun y => s (𝔄.ι y)) hsa
      (realAlg E B Q Γ t (fun y => (t y).val χa χb) 𝔄 a₀ g s hG.ok hK hT hb
        (by rw [hsa a₀ ha, hv]; exact one_ne_zero)))
  obtain ⟨R, hR, hrep⟩ := wordRep E B χa χb {γ // arch γ} (fun γ => t γ) (t a₀) J c w hHa hHb (hG.ok a₀)
    (fun γ => ⟨hG.ok γ, hψ γ γ.2⟩) hmul hadj
  refine ⟨_, R, hR, ?_, hnorm⟩
  rw [hval, hv, one_mul] at hrep
  exact hrep

end UpperTheory.Zero.ConvolutionTheory.EB
