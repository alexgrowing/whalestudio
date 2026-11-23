import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.Fresh

variable {F : Type} [Field F] [NumberField F]

theorem ordI_mul_of_ne_bot (v : HeightOneSpectrum (𝓞 F)) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ordI v (I * J) = ordI v I + ordI v J := by
  unfold ordI
  rw [← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ)
    v.associates_irreducible

theorem ordI_asIdeal_self (w : HeightOneSpectrum (𝓞 F)) : ordI w w.asIdeal = 1 := by
  unfold ordI
  exact Associates.count_self w.associates_irreducible

theorem hasDerivAt_chart_curve [IsTotallyReal F] (f : GA F 2 → ℂ) (g : GA F 2)
    (hd : DifferentiableAt ℝ (UpperTheory.V.TR.chart f g) (UpperTheory.V.TR.oneL F 2))
    (k : ℝ → GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (X : UpperTheory.V.TR.Lie F 2) (h0 : k 0 = 1)
    (hk : HasDerivAt (fun t => UpperTheory.V.TR.toL (k t).val) X 0) :
    HasDerivAt (fun t => f (g * UpperTheory.V.TR.infGL F 2 (k t))) (UpperTheory.V.TR.lieD X f g) 0 := by
  unfold UpperTheory.V.TR.lieD
  have hf := hd.hasFDerivAt
  have hpt : UpperTheory.V.TR.oneL F 2 = (fun t => UpperTheory.V.TR.toL (k t).val) 0 := by
    simp only [h0, Units.val_one]
  rw [hpt] at hf
  have := hf.comp_hasDerivAt 0 hk
  rw [← hpt] at this
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  exact (UpperTheory.V.TR.chart_val f g (k t)).symm

end UpperTheory.HilbertEisensteinWeightOne.Fresh
