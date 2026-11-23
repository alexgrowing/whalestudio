import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ActHcsSlice
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.LogSizeInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.ConvMul
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbConv

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH finH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem convMul : ConvMul := by
  intro E _ _ _ B f hf
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  refine ⟨fun t t' ht ht' => ?_, fun ψ ψ' hψ hψ' => ?_⟩
  · have hT := PositivityTheory.Rg.BcB.F.Op.test B tensTest t ht
    have hT' := PositivityTheory.Rg.BcB.F.Op.test B tensTest t' ht'
    have hm := (tensMul E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb
      t.T t'.T t.ψ t'.ψ B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ).2
    have e : (t.mul t').Φ = mulM B.D.μ t.Φ t'.Φ := hm.symm
    rw [e]
    exact PositivityTheory.Rg.BcB.F.Rd.B.conv_mulM B.D t.Φ t'.Φ hT hT' f hf
  · have hcf : Continuous fun h : Hf E B.a B.b => finH h :=
      ((continuous_finGL' B.a).comp continuous_fst).prodMk ((continuous_finGL' B.b).comp continuous_snd)
    have hF : ∀ i x, Continuous fun h => f i (x * finH h) := fun i x =>
      (hf i).comp (continuous_const.mul hcf)
    have hI : ∀ (φ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)), IsFinM φ → ∀ y z i x,
        Integrable (fun h => φ y z h * f i (x * finH h)) B.ν := fun φ hφ y z i x =>
      ((hφ y z).1.mul (hF i x)).integrable_of_hasCompactSupport (hφ y z).2.mul_right
    refine ⟨PositivityTheory.Rg.BcB.F.R3.convF_mulF_eq_convF_convF B.ν ψ ψ' hψ hψ' f hF, ?_, fun c => ⟨?_, ?_⟩⟩
    · funext i x
      simp only [convF, Pi.add_apply, Matrix.add_apply, add_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      exact integral_add (hI ψ hψ _ _ _ _) (hI ψ' hψ' _ _ _ _)
    · funext i x
      simp only [convF, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      exact integral_const_mul _ _
    · funext i x
      simp only [convF, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      show ψ i.2 z h * (c * f (i.1, z) (x * finH h)) = c * (ψ i.2 z h * f (i.1, z) (x * finH h))
      ring

end UpperTheory.Zero.ConvolutionTheory.EB
