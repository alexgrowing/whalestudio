import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HkComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.MemULOfSplit

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

theorem genSt : GenSt := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T e₁ e₂
  have hPt := ptOk E a b l₁ l₂ D A
  have hMul := hkMul E a b l₁ l₂ D A S Z L hS hZ
  have hComm := hkComm E a b l₁ l₂ D A S Z L hS hZ
  have hidm : ∀ e e', A.hk S L ∅ e e' = A.idm S L := hMul.2.2.2.2.1
  have hfin : ∀ T' e e', IsFinM (A.hk S L T' e e') := fun T' e e' => (hMul.2.2.2.2.2.2.1 T' e e').1

  have hform : ∀ γ : Gam a b S Z, ∃ wa wb T' e e',
      A.gen S L T e₁ e₂ γ = A.pt wa wb (A.hk S L T' e e') := by
    rintro (_ | x | x | _)
    · exact ⟨_, _, ∅, fun _ => .one, fun _ => .one, by
        rw [hidm]; rfl⟩
    · exact ⟨_, _, ∅, fun _ => .one, fun _ => .one, by
        rw [hidm]; rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
  have hok : ∀ γ, (A.gen S L T e₁ e₂ γ).Ok := by
    intro γ
    obtain ⟨wa, wb, T', e, e', h⟩ := hform γ
    rw [h]
    exact hPt.2.2.1 wa wb _ (hfin T' e e')
  refine ⟨⟨hok, ?_, ?_⟩, ?_⟩
  · intro x y
    obtain ⟨wa, wb, T', e, e', h⟩ := hform x
    obtain ⟨wa', wb', T'', f, f', h'⟩ := hform y
    have hx := hok x
    have hy := hok y
    rw [h] at hx ⊢
    rw [h'] at hy ⊢
    exact BlockFiniteConvolution.blkComm₀ E A.blk _ _ hx hy (hComm T' T'' e e' f f').1
  · intro x y
    obtain ⟨wa, wb, T', e, e', h⟩ := hform x
    obtain ⟨wa', wb', T'', f, f', h'⟩ := hform y
    have hx := hok x
    have hy := hok y
    rw [h] at hx ⊢
    rw [h'] at hy ⊢
    have hop := BlockFiniteConvolution.blkOp₀ E A.blk _ _ hy hy
    rw [ContinuousLinearMap.star_eq_adjoint, ← hop.2.2.2.2.2.1]
    exact BlockFiniteConvolution.blkComm₀ E A.blk _ _ hx hop.2.2.2.2.1 (hComm T' T'' e e' f f').2
  · haveI : Countable (Pl E) := Small.countable_pl E
    infer_instance

end UpperTheory.Zero.ConvolutionTheory.EB
