import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierInfinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

open NumberField.mixedEmbedding NumberField.InfinitePlace Function
open scoped SchwartzMap FourierTransform Real Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def levelIdeal (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_levelIdeal {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((levelIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w := by
  unfold levelIdeal
  rw [count_finprod_primeIdealUnit_zpow]
  refine Filter.eventually_cofinite.2 (hc.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq, Nat.cast_eq_zero] at hv ⊢
  exact hv

theorem mem_level_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (B : Af F) :
    B ∈ idealFiniteAdeles (levelIdeal c) ↔ ∀ w, Valued.v (pLoc F w B) ≤ WithZero.exp (-(c w : ℤ)) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_levelIdeal hc]
  rfl

theorem count_different (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = dd w := by
  rw [FractionalIdeal.count_coe F w (differentIdeal_ne_bot (A := ℤ))]
  rfl

theorem mem_dual_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (Z : Af F) :
    Z ∈ idealFiniteAdeles (traceDualIdeal F (levelIdeal c)) ↔
      ∀ w, Valued.v (pLoc F w Z) ≤ WithZero.exp ((c w : ℤ) + dd w) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_traceDualIdeal, count_levelIdeal hc, count_different, neg_neg]
  rfl

theorem isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩

theorem prod_real (f : InfinitePlace F → ℂ) : ∏ w : {w : InfinitePlace F // IsReal w}, f w.1 = ∏ v, f v :=
  (Equiv.subtypeUnivEquiv (fun w : InfinitePlace F => IsTotallyReal.isReal w)).prod_comp f

def archPoly (a : InfinitePlace F → ℝ) (x : mixedSpace F) : ℂ :=
  ∏ w : {w : InfinitePlace F // IsReal w},
    (((a w.1 : ℝ) : ℂ) + Complex.I * ((x.1 w : ℝ) : ℂ)) * Complex.exp (-(π : ℂ) * ((a w.1 : ℝ) : ℂ) ^ 2)

theorem hasTemperateGrowth_archPoly (a : InfinitePlace F → ℝ) : (archPoly (F := F) a).HasTemperateGrowth := by
  unfold archPoly
  refine hasTemperateGrowth_finsetProd _ fun w _ => ?_
  have hlin : (fun x : mixedSpace F => ((x.1 w : ℝ) : ℂ)).HasTemperateGrowth :=
    ((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w // IsReal w} → ℝ)
        ({w // IsComplex w} → ℂ))) : mixedSpace F →L[ℝ] ℂ)).hasTemperateGrowth
  exact ((HasTemperateGrowth.const _).add ((HasTemperateGrowth.const Complex.I).mul hlin)).mul
    (HasTemperateGrowth.const _)

def archSchwartz (a : InfinitePlace F → ℝ) : 𝓢(mixedSpace F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (archPoly a)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
      (gaussianSchwartz (euclidean.mixedSpace F)))

theorem archSchwartz_apply (a : InfinitePlace F → ℝ) (x : mixedSpace F) :
    archSchwartz a x = archPoly a x * ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [archSchwartz, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_archPoly a),
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]

theorem archSchwartz_eq_prod (a : InfinitePlace F → ℝ) (x : mixedSpace F) :
    archSchwartz a x = ∏ w : {w : InfinitePlace F // IsReal w},
      (((a w.1 : ℝ) : ℂ) + Complex.I * ((x.1 w : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + ((x.1 w : ℝ) : ℂ) ^ 2)) := by
  haveI := isEmpty_complex (F := F)
  rw [archSchwartz_apply, archPoly, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}),
    Finset.sum_empty, mul_zero, add_zero, Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem archSchwartz_homeo (A B : Ad F) :
    archSchwartz (UpperTheory.V.TR.pInf F A) (homeomorphMixedSpace F B.1) =
      arch (UpperTheory.V.TR.pInf F A) (UpperTheory.V.TR.pInf F B) := by
  rw [archSchwartz_eq_prod, arch]
  exact prod_real (fun v => (((UpperTheory.V.TR.pInf F A v : ℝ) : ℂ) + Complex.I * ((UpperTheory.V.TR.pInf F B v : ℝ) : ℂ)) *
    Complex.exp (-(π : ℂ) * (((UpperTheory.V.TR.pInf F A v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F B v : ℝ) : ℂ) ^ 2)))

open Classical in
theorem slice_eq {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A : Ad F) :
    slice c A = (if ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) then (1 : ℂ) else 0) •
      schwartzBruhatTensor (archSchwartz (UpperTheory.V.TR.pInf F A)) (cosetIndicator (levelIdeal c) 1) := by
  funext B
  simp only [slice, Phi, Pi.smul_apply, smul_eq_mul, schwartzBruhatTensor, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [archSchwartz_homeo, cosetIndicator_apply, mem_level_iff hc]
  have hB : ∀ w, pLoc F w (B.2 - 1) = pLoc F w (pFin F B) - 1 := fun w => by
    rw [map_sub, map_one]; rfl
  simp only [hB]
  by_cases h1 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))
  · by_cases h2 : ∀ w, Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ))
    · have h3 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
          Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun w => ⟨h1 w, h2 w⟩
      simp only [forall_and, h1, h2, and_self, implies_true, ↓reduceIte, mul_one, one_mul]
    · have h3 : ¬ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
          Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun h => h2 fun w => (h w).2
      simp only [forall_and, h1, h2, true_and, and_false, ↓reduceIte, mul_zero, one_mul]
  · have h3 : ¬ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun h => h1 fun w => (h w).1
    simp only [forall_and, h1, false_and, ↓reduceIte, mul_zero, zero_mul]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem slice_mem_sb {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A : Ad F) :
    slice c A ∈ schwartzBruhat F := by
  rw [L1.slice_eq hc A]
  exact Submodule.smul_mem _ _ (schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat _ _))

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
