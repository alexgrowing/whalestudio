import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private noncomputable def gaussEquiv (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ι : Type) [Fintype ι] :
    (ι → NumberField.mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (ι × InfinitePlace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => WithLp.toLp 2 fun p => (x p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩
      map_add' := fun x y => by ext p; simp
      map_smul' := fun c x => by ext p; simp
      invFun := fun y i => (fun w => y (i, w.1), fun _ => 0)
      left_inv := fun x => by
        funext i
        refine Prod.ext (funext fun w => rfl) (funext fun w => ?_)
        exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)
      right_inv := fun y => by ext p; rfl }

private theorem gaussEquiv_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ι : Type} [Fintype ι]
    (v : ι → A F) (p : ι × InfinitePlace F) :
    gaussEquiv F ι (infPartPi v) p = TR.pInf F (v p.1) p.2 := by
  change (infPartPi v p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩ = _
  simp only [infPartPi, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change _ = InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2) ((v p.1).1 p.2)
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]

theorem UpperTheory.ConvolutionTheory.R2.C.gaussS :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ι : Type) [Fintype ι] (g : FiniteAdeleRing (𝓞 F) F → ℂ), g ∈ finiteSchwartzBruhat F → (fun v : ι → A F => ∏ i, g1 g (v i)) ∈ schwartzBruhatPi F ι := by
  intro F _ _ _ ι _ g hg
  have h := schwartzBruhatTensorPi_mem
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussEquiv F ι)
      (gaussianSchwartz (EuclideanSpace ℝ (ι × InfinitePlace F))))
    (finiteTensor_mem (ι := ι) fun _ => hg)
  convert h using 1
  funext v
  have hn : ‖gaussEquiv F ι (infPartPi v)‖ ^ 2 = ∑ i, ∑ w, TR.pInf F (v i) w ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by rw [gaussEquiv_apply]
  simp only [schwartzBruhatTensorPi, finiteTensor, g1, Finset.prod_mul_distrib,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply, hn]
  congr 1
  · push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    refine (Finset.prod_congr rfl fun i _ => ?_)
    rw [Finset.mul_sum, Complex.exp_sum]
