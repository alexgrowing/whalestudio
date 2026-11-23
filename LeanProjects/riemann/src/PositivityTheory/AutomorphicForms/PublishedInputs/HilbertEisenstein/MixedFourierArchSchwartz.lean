import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HasTemperateGrowthArchPoly
import GroundTheory.GlobalFields.TateThesis.ConductorIdeal
import GroundTheory.GlobalFields.TateThesis.Conductor
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

open NumberField.mixedEmbedding NumberField.InfinitePlace Function
open scoped SchwartzMap FourierTransform Real Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem mem_units_of_isUnitAt (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    x ∈ (Submonoid.ofClass (w.adicCompletionIntegers F)).units := by
  rw [Submonoid.mem_units_iff]
  have hx' : Valued.v (x : w.adicCompletion F) = 1 := hx
  refine ⟨?_, ?_⟩
  · change (x : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx']
  · change ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hx', inv_one]

theorem integral_arch_one (a y : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) *
        (((a : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))) =
      ((a : ℂ) + (y : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (y : ℂ) ^ 2)) := by
  set c1 : ℂ := (a : ℂ) * Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2)
  set c2 : ℂ := Complex.I * Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2)
  have hpt : ∀ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) *
      (((a : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))) =
      c1 * (((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t) +
        c2 * (((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t) := by
    intro t
    simp only [c1, c2, realGaussian, realGaussianOdd]
    have : Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2)) =
        Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2) * Complex.exp (-(π : ℂ) * (t : ℂ) ^ 2) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this]
    ring
  have hce : Continuous fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hg : Continuous realGaussian := by unfold realGaussian; fun_prop
  have hgo : Continuous realGaussianOdd := by unfold realGaussianOdd; fun_prop
  have hi1 : Integrable fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t :=
    integrable_realGaussian.norm.mono' (hce.mul hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_mul, Circle.norm_coe, one_mul])
  have hi2 : Integrable fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t :=
    integrable_realGaussianOdd.norm.mono' (hce.mul hgo).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_mul, Circle.norm_coe, one_mul])
  have hf1 : 𝓕 realGaussian y = ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t := by
    rw [Real.fourier_real_eq]; simp only [Circle.smul_def, smul_eq_mul]
  have hf2 : 𝓕 realGaussianOdd y = ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t := by
    rw [Real.fourier_real_eq]; simp only [Circle.smul_def, smul_eq_mul]
  simp only [hpt]
  rw [integral_add (hi1.const_mul c1) (hi2.const_mul c2), integral_const_mul, integral_const_mul, ← hf1, ← hf2,
    fourier_realGaussian, fourier_realGaussianOdd]
  simp only [c1, c2, realGaussian, realGaussianOdd]
  have : Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (y : ℂ) ^ 2)) =
      Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2) * Complex.exp (-(π : ℂ) * (y : ℂ) ^ 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem mixedFourier_archSchwartz (a : InfinitePlace F → ℝ) (Z : Ad F) :
    mixedFourier F (archSchwartz a) (homeomorphMixedSpace F Z.1) =
      ∏ v, (((a v : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ) ^ 2)) := by
  haveI := isEmpty_complex (F := F)
  set m := homeomorphMixedSpace F Z.1
  set A : ∀ w : {w : InfinitePlace F // IsReal w}, ℝ → ℂ := fun w t => ((𝐞 (-(t * m.1 w)) : Circle) : ℂ) *
    ((((a w.1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + (t : ℂ) ^ 2)))
  set B : ∀ w : {w : InfinitePlace F // IsComplex w}, ℂ → ℂ := fun _ _ => 1
  have hint : ∀ x : mixedSpace F, 𝐞 (-mixedTraceForm F x m) • archSchwartz a x =
      (∏ w, A w (x.1 w)) * ∏ w, B w (x.2 w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, HeckeCharacter.fourierChar_neg_mixedTraceForm, archSchwartz_eq_prod]
    simp only [A, B, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}), Finset.prod_empty,
      mul_one, Finset.prod_mul_distrib]
  have hA : ∀ w : {w : InfinitePlace F // IsReal w}, ∫ t, A w t =
      (((a w.1 : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z w.1 : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z w.1 : ℝ) : ℂ) ^ 2)) :=
    fun w => integral_arch_one (a w.1) (m.1 w)
  rw [mixedFourier_apply, selfDualMeasure, integral_smul_measure, Measure.volume_eq_prod]
  simp only [hint]
  rw [integral_prod_mul (f := fun x : {w : InfinitePlace F // IsReal w} → ℝ ↦ ∏ w, A w (x w))
    (g := fun z : {w : InfinitePlace F // IsComplex w} → ℂ ↦ ∏ w, B w (z w)),
    integral_fintype_prod_volume_eq_prod, integral_fintype_prod_volume_eq_prod]
  simp only [hA, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}), Finset.prod_empty, mul_one,
    IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, ENNReal.toReal_one, one_smul]
  exact prod_real (fun v => (((a v : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ) ^ 2)))

theorem adelicFourier_slice {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A Z : Ad F) :
    adelicFourier F (slice c A) Z =
      ((finiteAdeleMeasure F (idealFiniteAdeles (levelIdeal c))).toReal : ℂ) * kernF c A Z := by
  classical
  rw [slice_eq hc A, adelicFourier_smul, Pi.smul_apply, adelicFourier_schwartzBruhatTensor, schwartzBruhatTensor,
    mixedFourierSchwartz_apply, finiteFourier_cosetIndicator, mixedFourier_archSchwartz, smul_eq_mul, one_mul]
  unfold kernF
  rw [Set.indicator_apply]
  simp only [SetLike.mem_coe, Pi.one_apply]
  rw [mem_dual_iff hc]
  have hZ : Z.2 = pFin F Z := rfl
  rw [hZ]
  by_cases h1 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))
  · by_cases h2 : ∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)
    · simp only [h1, h2, and_self, implies_true, ↓reduceIte]; ring
    · simp only [h1, h2, implies_true, true_and, ↓reduceIte]; ring
  · simp only [h1, false_and, ↓reduceIte]; ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

theorem finite_expansion_holds : SFin := by
  intro F _ _ _ ω c H
  set χ : (FiniteAdeleRing (𝓞 F) F)ˣ →* ℂˣ := ω.1.comp IdeleGroup.ofFinite with hχdef
  have hχ : Continuous χ := ω.2.1.comp IdeleGroup.continuous_ofFinite
  refine (IdeleGroup.finite_support_conductorExponentAt Complex.units_noSmallSubgroups χ hχ).subset ?_
  intro w hw
  rw [Function.mem_support]
  intro h0
  apply hw
  have hk := (IdeleGroup.conductorExponentAt_eq_zero_iff Complex.units_noSmallSubgroups χ hχ w).1 h0
  have hmem : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} := by
    intro x hx _
    have h1 := hk (mem_units_of_isUnitAt w x hx)
    rw [MonoidHom.mem_ker] at h1
    exact h1
  exact Nat.le_zero.1 ((H.cond w).2 hmem)

theorem kernel_expansion_holds : SKern := by
  intro F _ _ _ c hc
  refine ⟨((finiteAdeleMeasure F (idealFiniteAdeles (levelIdeal c))).toReal : ℂ), ?_,
    fun A Z => adelicFourier_slice hc A Z⟩
  rw [Complex.ofReal_ne_zero, finiteAdeleMeasure_idealFiniteAdeles_toReal]
  refine mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)
  · rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact (levelIdeal c).ne_zero
  · rw [NNReal.coe_ne_zero, Ne, NNReal.sqrt_eq_zero, nnnorm_eq_zero]
    exact_mod_cast NumberField.discr_ne_zero F

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
