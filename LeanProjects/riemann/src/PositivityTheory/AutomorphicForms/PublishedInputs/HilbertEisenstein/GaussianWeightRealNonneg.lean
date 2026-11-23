import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.P5meas

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Classical nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.CharpolyCoeffsInSubalgebra

open L5

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem hasTemperateGrowth_wpoly : (wpoly F).HasTemperateGrowth := by
  unfold wpoly
  refine hasTemperateGrowth_finsetProd _ fun v _ => ?_
  have hL := ((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj
    (⟨v, IsTotallyReal.isReal v⟩ : {w : InfinitePlace F // IsReal w}) :
      ({w : InfinitePlace F // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ
        ({w : InfinitePlace F // IsReal w} → ℝ) ({w : InfinitePlace F // IsComplex w} → ℂ))) :
          mixedSpace F →L[ℝ] ℂ)).hasTemperateGrowth
  have h1 : (fun _ : mixedSpace F => (1 : ℂ)).HasTemperateGrowth := by fun_prop
  exact h1.add (hL.pow 2)

instance isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩

def rp (v : InfinitePlace F) : {w : InfinitePlace F // IsReal w} := ⟨v, IsTotallyReal.isReal v⟩

theorem gaussian_weight_apply (x : mixedSpace F) :
    phi1 F x = ((∏ v : InfinitePlace F, ((1 + (x.1 (rp v)) ^ 2) * Real.exp (-Real.pi * (x.1 (rp v)) ^ 2)) : ℝ) : ℂ) := by
  rw [phi1, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_wpoly,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]
  have hc : ∑ w : {w : InfinitePlace F // IsComplex w}, ‖x.2 w‖ ^ 2 = 0 := Finset.sum_of_isEmpty _
  have hs : ∑ w : {w : InfinitePlace F // IsReal w}, x.1 w ^ 2 = ∑ v : InfinitePlace F, x.1 (rp v) ^ 2 := by
    refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun w => ?_
    rfl
  rw [hc, mul_zero, add_zero, hs, Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_prod, wpoly]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    push_cast
    rfl

theorem pos_factor (a : ℝ) : 0 < (1 + a ^ 2) * Real.exp (-Real.pi * a ^ 2) :=
  mul_pos (by positivity) (Real.exp_pos _)

theorem gaussian_weight_real_nonneg (x : mixedSpace F) : ∃ r : ℝ, 0 ≤ r ∧ phi1 F x = (r : ℂ) :=
  ⟨_, (Finset.prod_pos fun v _ => pos_factor _).le, gaussian_weight_apply x⟩

theorem norm_real_test_matrix (x : mixedSpace F) :
    ‖phi1 F x‖ = ∏ v : InfinitePlace F, ((1 + (x.1 (rp v)) ^ 2) * Real.exp (-Real.pi * (x.1 (rp v)) ^ 2)) := by
  rw [gaussian_weight_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Finset.prod_pos fun v _ => pos_factor _)]

theorem hms_fst (x : InfiniteAdeleRing F) (v : InfinitePlace F) :
    (homeomorphMixedSpace F x).1 (rp v) = (UpperTheory.V.TR.infEq F).symm x v := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal _ (x v) =
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.symm (x v)
  rw [RingEquiv.symm_symm, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]

theorem place_bound (a z : ℝ) :
    |a + z| * Real.exp (-Real.pi * (a ^ 2 + z ^ 2)) ≤
      ((1 + a ^ 2) * Real.exp (-Real.pi * a ^ 2)) * ((1 + z ^ 2) * Real.exp (-Real.pi * z ^ 2)) := by
  have he : Real.exp (-Real.pi * (a ^ 2 + z ^ 2)) = Real.exp (-Real.pi * a ^ 2) * Real.exp (-Real.pi * z ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : |a + z| ≤ (1 + a ^ 2) * (1 + z ^ 2) := by
    have e1 := sq_abs a
    have e2 := sq_abs z
    have e3 := sq_nonneg (abs a - 1 / 2)
    have e4 := sq_nonneg (abs z - 1 / 2)
    have e5 := mul_nonneg (sq_nonneg a) (sq_nonneg z)
    have e6 := abs_add_le a z
    nlinarith
  rw [he]
  have hp1 := Real.exp_pos (-Real.pi * a ^ 2)
  have hp2 := Real.exp_pos (-Real.pi * z ^ 2)
  calc |a + z| * (Real.exp (-Real.pi * a ^ 2) * Real.exp (-Real.pi * z ^ 2))
      ≤ ((1 + a ^ 2) * (1 + z ^ 2)) * (Real.exp (-Real.pi * a ^ 2) * Real.exp (-Real.pi * z ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := by ring

theorem norm_place (a z : ℝ) :
    ‖((a : ℂ) + (z : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (z : ℂ) ^ 2))‖ =
      |a + z| * Real.exp (-Real.pi * (a ^ 2 + z ^ 2)) := by
  have h : -(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (z : ℂ) ^ 2) = ((-Real.pi * (a ^ 2 + z ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_ofReal, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]

theorem mem_one_of_condA {c : HeightOneSpectrum (𝓞 F) → ℕ} {A : Ad F}
    (h : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))) :
    A.2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) := by
  rw [mem_idealFiniteAdeles]
  intro v
  rw [Units.val_one, FractionalIdeal.count_one, neg_zero]
  exact (h v).trans (WithZero.exp_le_exp.2 (by omega))

theorem standard_hermitian_apply (x : Ad F) : H1 F x = phi1 F (homeomorphMixedSpace F x.1) * cosetIndicator 1 0 x.2 := rfl

theorem cosetIndicator_one_of_mem {z : Af F} (h : z ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) :
    cosetIndicator 1 0 z = 1 := by
  rw [cosetIndicator_apply, sub_zero, if_pos h]

theorem cosetIndicator_real (z : Af F) : ∃ r : ℝ, 0 ≤ r ∧ cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) 0 z = (r : ℂ) := by
  rw [cosetIndicator_apply]
  split_ifs
  · exact ⟨1, zero_le_one, by simp⟩
  · exact ⟨0, le_rfl, by simp⟩

theorem arch_norm (A Z : Ad F) :
    ‖∏ v, (((UpperTheory.V.TR.pInf F A v : ℂ) + (UpperTheory.V.TR.pInf F Z v : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((UpperTheory.V.TR.pInf F A v : ℂ) ^ 2 + (UpperTheory.V.TR.pInf F Z v : ℂ) ^ 2)))‖ ≤
      ‖phi1 F (homeomorphMixedSpace F A.1)‖ * ‖phi1 F (homeomorphMixedSpace F Z.1)‖ := by
  rw [norm_prod, norm_real_test_matrix, norm_real_test_matrix, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
  rw [norm_place, hms_fst, hms_fst]
  exact place_bound _ _

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.CharpolyCoeffsInSubalgebra

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L5 CharpolyCoeffsInSubalgebra

theorem dominating_function_holds : P5dom := by
  intro F _ _ _
  refine ⟨schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat _ _), ?_, ?_⟩
  · intro x
    obtain ⟨r, hr, hr'⟩ := gaussian_weight_real_nonneg (homeomorphMixedSpace F x.1)
    obtain ⟨s, hs, hs'⟩ := cosetIndicator_real (F := F) x.2
    rw [standard_hermitian_apply, hr', hs', ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr hs)]
  · intro c A Z Z' h1 h2
    unfold kernF
    split_ifs with h
    · rw [norm_mul, Circle.norm_coe, mul_one, standard_hermitian_apply, standard_hermitian_apply, norm_mul, norm_mul,
        cosetIndicator_one_of_mem (mem_one_of_condA h.1), cosetIndicator_one_of_mem (h2 h.2), norm_one, mul_one,
        mul_one, h1]
      exact arch_norm A Z
    · rw [mul_zero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
