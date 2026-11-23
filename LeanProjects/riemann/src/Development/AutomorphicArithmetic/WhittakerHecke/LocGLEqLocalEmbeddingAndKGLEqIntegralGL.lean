import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import GroundTheory.GlobalFields.LocalFieldAtPlace

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

theorem UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)),
          (∀ g, GlobalTheory.CuspRep.locGL E n w g = AdelicGLn.localEmbedding w g) ∧
          GlobalTheory.LFun.KGL w n = GLnLocal.integralGL (w.adicCompletion E) n := by
  intro E _ _ n w
  refine ⟨fun g => ?_, ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
    have key : ∀ v, Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (GlobalTheory.CuspRep.locGL E n w g) =
        Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (AdelicGLn.localEmbedding w g) := fun v => by
      by_cases h : v = w
      · subst h
        rw [GlobalTheory.CuspRep.pLoc_locGL]
        exact (h1 g).symm
      · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne h]
        exact (h2 v h g).symm
    refine Units.ext (Matrix.ext fun i j => ?_)
    refine DFunLike.ext _ _ fun v => ?_
    exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (key v)
  · have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
        Formalism.UG.GLint (Fin n) O = GLnLocal.integralGL (w.adicCompletion E) n := by
      rintro _ rfl
      rfl
    exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)
