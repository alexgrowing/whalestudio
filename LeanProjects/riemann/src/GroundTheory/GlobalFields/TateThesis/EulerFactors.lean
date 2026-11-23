import Mathlib
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite
import GroundTheory.GlobalFields.TateThesis.GlobalZeta
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureCosets

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex
open scoped NumberField.AdeleRing Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def gammaFactor (s : ℂ) : ℂ := ∏ w, χ.infiniteGamma w s

omit [NumberField K] in
theorem prod_infiniteConst [NumberField K] :
    ∏ w : InfinitePlace K, infiniteConst w = (π : ℂ) ^ nrComplexPlaces K := by
  rw [prod_eq_prod_mul_prod]
  have h1 : ∀ w : {w : InfinitePlace K // IsReal w}, infiniteConst w.1 = 1 := fun w ↦ by
    rw [infiniteConst, if_pos w.2]
  have h2 : ∀ w : {w : InfinitePlace K // IsComplex w}, infiniteConst w.1 = π := fun w ↦ by
    rw [infiniteConst, if_neg (not_isReal_iff_isComplex.2 w.2)]
  simp only [h1, h2, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ]

def testFunction : 𝔸[K] → ℂ := schwartzBruhatTensor χ.infiniteSchwartz χ.finiteTestFun

theorem pi_pow_nrComplexPlaces_ne_zero : (π : ℂ) ^ nrComplexPlaces K ≠ 0 :=
  pow_ne_zero _ (ofReal_ne_zero.2 Real.pi_ne_zero)

theorem testFunction_mem : χ.testFunction ∈ schwartzBruhat K :=
  schwartzBruhatTensor_mem _ χ.finiteTestFun_mem

theorem zetaIntegrand_testFunction (s : ℂ) (x : IdeleGroup K) :
    χ.testFunction x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s =
      (χ.infiniteSchwartz (homeomorphMixedSpace K (toInfinite K x)) *
          (χ.toIdele (ofInfinite (toInfinite K x)) : ℂ) *
          ((∏ w, ‖((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult :
            ℝ) : ℂ) ^ s) *
        (χ.finiteTestFun (toFinite K x) * (χ.toIdele (ofFinite (toFinite K x)) : ℂ) *
          ((finiteModule (ofFinite (toFinite K x)) : ℝ) : ℂ) ^ s) := by
  have hchi : (χ.toIdele x : ℂ) = (χ.toIdele (ofFinite (toFinite K x)) : ℂ) *
      (χ.toIdele (ofInfinite (toInfinite K x)) : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, ofFinite_mul_ofInfinite]
  have hmod : ((ideleModule K x : ℝ) : ℂ) ^ s =
      ((∏ w, ‖((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult :
        ℝ) : ℂ) ^ s * ((finiteModule (ofFinite (toFinite K x)) : ℝ) : ℂ) ^ s := by
    rw [ideleModule_apply, ofReal_mul, mul_cpow_ofReal_nonneg (infiniteModule_pos x).le
      (finiteModule_pos x).le]
    rfl
  rw [hchi, hmod]
  change χ.infiniteSchwartz (homeomorphMixedSpace K (x : 𝔸[K]).1) * χ.finiteTestFun (x : 𝔸[K]).2 *
    _ * _ = _
  have e1 : (x : 𝔸[K]).1 = ((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) :=
    rfl
  have e2 : (x : 𝔸[K]).2 = ((toFinite K x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    FiniteAdeleRing (𝓞 K) K) := rfl
  rw [e1, e2]
  ring

theorem globalZeta_testFunction {s : ℂ} (hs : 1 < s.re) :
    globalZeta χ.testFunction χ s = (π : ℂ) ^ nrComplexPlaces K * χ.gammaFactor s * χ.LFunction s := by
  have hs0 : 0 < s.re := by linarith
  set A : (InfiniteAdeleRing K)ˣ → ℂ := fun a ↦ χ.infiniteSchwartz (homeomorphMixedSpace K a) *
    (χ.toIdele (ofInfinite a) : ℂ) * ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s
    with hA
  set B : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ := fun b ↦ χ.finiteTestFun b *
    (χ.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) : ℝ) : ℂ) ^ s with hB
  have hF : ∀ x : IdeleGroup K, χ.testFunction x * (χ.toIdele x : ℂ) *
      ((ideleModule K x : ℝ) : ℂ) ^ s = A (toInfinite K x) * B (toFinite K x) :=
    χ.zetaIntegrand_testFunction s
  have hBinv : ∀ b, ∀ w ∈ finiteIntegralUnits K, B (b * w) = B b := fun b w hw ↦ by
    simp only [hB, χ.finiteTestFun_mul_toIdele_mul_cpow, ordFinsupp_ofFinite_mul b hw]
  have hinv : ∀ x : IdeleGroup K, ∀ w ∈ finiteIntegralUnits K,
      χ.testFunction (x * (prodEquiv K).symm (1, w) : IdeleGroup K) *
        (χ.toIdele (x * (prodEquiv K).symm (1, w)) : ℂ) *
        ((ideleModule K (x * (prodEquiv K).symm (1, w)) : ℝ) : ℂ) ^ s =
      χ.testFunction x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s := by
    intro x w hw
    rw [hF, hF, map_mul, map_mul]
    have h1 : toInfinite K ((prodEquiv K).symm (1, w)) = 1 := by
      change ((prodEquiv K) ((prodEquiv K).symm (1, w))).1 = 1
      rw [ContinuousMulEquiv.apply_symm_apply]
    have h2 : toFinite K ((prodEquiv K).symm (1, w)) = w := by
      change ((prodEquiv K) ((prodEquiv K).symm (1, w))).2 = w
      rw [ContinuousMulEquiv.apply_symm_apply]
    rw [h1, h2, mul_one, hBinv _ w hw]
  have h := hasSum_integral_ideleMeasure_of_invariant_finiteIntegralUnits
    (integrable_globalZetaIntegrand χ.testFunction_mem χ hs) hinv
  have hc : ∀ c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K,
      ∫ a, χ.testFunction ((prodEquiv K).symm (a, c.out) : IdeleGroup K) *
        (χ.toIdele ((prodEquiv K).symm (a, c.out)) : ℂ) *
        ((ideleModule K ((prodEquiv K).symm (a, c.out)) : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure K =
      (∏ w, infiniteConst w * χ.infiniteGamma w s) * B c.out := by
    intro c
    have hsymm : ∀ a, toInfinite K ((prodEquiv K).symm (a, c.out)) = a ∧
        toFinite K ((prodEquiv K).symm (a, c.out)) = c.out := fun a ↦ by
      constructor
      · change ((prodEquiv K) ((prodEquiv K).symm (a, c.out))).1 = a
        rw [ContinuousMulEquiv.apply_symm_apply]
      · change ((prodEquiv K) ((prodEquiv K).symm (a, c.out))).2 = c.out
        rw [ContinuousMulEquiv.apply_symm_apply]
    simp only [hF, (hsymm _).1, (hsymm _).2]
    rw [integral_mul_const, ← χ.integral_infiniteSchwartz hs0]
  simp only [hc] at h
  have h2 := (χ.hasSum_finiteTestFun hs).mul_left (∏ w, infiniteConst w * χ.infiniteGamma w s)
  rw [globalZeta, h.unique h2, Finset.prod_mul_distrib, prod_infiniteConst, gammaFactor]

end HeckeCharacter

end

end GroundTheory.Global
