import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private noncomputable def UpperTheory.ConvolutionTheory.R2.Fo.mix {F : Type} [Field F] [NumberField F] (g h : G1 F) : G1 F :=
  ⟨Matrix.of fun i j => ((g i j).1, (h i j).2), by
    have hg := g.det_coe
    have hh := h.det_coe
    rw [Matrix.det_fin_two] at hg hh ⊢
    have h1 := congrArg Prod.fst hg
    have h2 := congrArg Prod.snd hh
    exact Prod.ext h1 h2⟩

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_apply {F : Type} [Field F] [NumberField F] (g h : G1 F) (i j : Fin 2) :
    mix g h i j = ((g i j).1, (h i j).2) := rfl

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_one {F : Type} [Field F] [NumberField F] : mix (1 : G1 F) 1 = 1 := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  exact Prod.ext rfl rfl

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_mul {F : Type} [Field F] [NumberField F] (g h g' h' : G1 F) :
    mix (g * g') (h * h') = mix g h * mix g' h' := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change mix (g * g') (h * h') i j = (mix g h * mix g' h') i j
  rw [mix_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact Prod.ext rfl rfl

theorem UpperTheory.ConvolutionTheory.R2.Fo.proj :
    ∀ (F : Type) [Field F] [NumberField F], ∃ pi pf : G1 F →* G1 F, Continuous pf ∧ ∀ g, FinOne (pi g) ∧ InfOne (pf g) ∧ pi g * pf g = g ∧
    (∀ i j, (pi g i j).1 = (g i j).1) ∧ ∀ i j, (pf g i j).2 = (g i j).2 := by
  intro F _ _
  refine ⟨⟨⟨fun g => mix g 1, mix_one⟩, fun g h => ?_⟩, ⟨⟨fun g => mix 1 g, mix_one⟩, fun g h => ?_⟩, ?_, fun g => ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · change mix (g * h) 1 = mix g 1 * mix h 1
    rw [← mix_mul, one_mul]
  · change mix 1 (g * h) = mix 1 g * mix 1 h
    rw [← mix_mul, one_mul]
  · change Continuous fun g : G1 F => mix 1 g
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    have h : Continuous fun g : G1 F => g i j :=
      (continuous_apply_apply i j).comp continuous_subtype_val
    exact continuous_const.prodMk (continuous_snd.comp h)
  · change mix g 1 * mix 1 g = g
    rw [← mix_mul, one_mul, mul_one]
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    exact Prod.ext rfl rfl
