import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZero

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Host (HChar)
open GlobalTheory.LFun GlobalTheory.HeckeOne
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

namespace GlobalTheory.Published

def HeckeLPartialContinuation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))), T.Finite →
    (∀ χ : HChar K, χ.IsUnitary → (¬ ∃ t : ℝ, IsNormPow χ t) →
      ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ s : ℂ, 1 < s.re → Λ s = heckeL T χ s) ∧ ∀ s : ℂ, 1 ≤ s.re → Λ s ≠ 0) ∧
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * zetaOff T s) ∧
      ∀ s : ℂ, 1 ≤ s.re → Z s ≠ 0

end GlobalTheory.Published

namespace GlobalTheory.HeckePartial

variable {K : Type} [Field K] [NumberField K]

def removed (T : Finset (HeightOneSpectrum (𝓞 K))) (χ : HChar K) (s : ℂ) : ℂ :=
  ∏ w ∈ T, eulerPoly (heckeFam χ w) (npow w (-s))

theorem differentiable_removed (T : Finset (HeightOneSpectrum (𝓞 K))) (χ : HChar K) :
    Differentiable ℂ (removed T χ) :=
  Differentiable.fun_finsetProd fun _ _ => differentiable_eulerPoly _ _

theorem eulerPoly_heckeFam_ne_zero {χ : HChar K} (hu : χ.IsUnitary) (w : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) : eulerPoly (heckeFam χ w) (npow w (-s)) ≠ 0 :=
  eulerPoly_ne_zero fun _ hb => ((bounded_heckeFam ∅ hu).norm_le le_rfl (Set.notMem_empty w) hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

theorem removed_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K))) {χ : HChar K} (hu : χ.IsUnitary) {s : ℂ}
    (hs : 0 < s.re) : removed T χ s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => eulerPoly_heckeFam_ne_zero hu w hs

theorem heckeL_eq_mul_removed (T : Finset (HeightOneSpectrum (𝓞 K))) {χ : HChar K} (hu : χ.IsUnitary) {s a : ℂ}
    (hs : 1 < s.re) (ha : HasProd (eulerFactor χ s) a) : heckeL (T : Set _) χ s = a * removed T χ s := by
  have h1 := (converges_heckeFam (T : Set _) hu hs).hasProd
  have h2 : HasProd (fun w => locL (heckeFam χ) w s) _ :=
    HasProd.mul_compl (s := (T : Set _)) (Finset.hasProd T fun w => locL (heckeFam χ) w s) h1
  have h3 : a = (∏ w ∈ T, locL (heckeFam χ) w s) * heckeL (T : Set _) χ s := by
    refine ha.unique ?_
    exact (funext (fun w => locL_heckeFam χ w s) : (fun w => locL (heckeFam χ) w s) = eulerFactor χ s) ▸ h2
  have h4 : (∏ w ∈ T, locL (heckeFam χ) w s) = (removed T χ s)⁻¹ := by
    rw [removed, ← Finset.prod_inv_distrib]; rfl
  have h5 := removed_ne_zero T hu (s := s) (by linarith)
  rw [h3, h4]
  field_simp

theorem eq_one_add_of_re {s : ℂ} (hs : s.re = 1) : s = 1 + (s.im : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im s, hs]
  simp

theorem IsHeckeL.ne_zero_of_one_le {χ : HChar K} (hu : χ.IsUnitary) (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) {Λ : ℂ → ℂ}
    (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 ≤ s.re) : Λ s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · rw [(hΛ.2 s hs).unique (hasProd_exp hu hs)]
    exact Complex.exp_ne_zero _
  · set t := s.im
    have hχ' : ¬ ∃ u : ℝ, IsNormPow (χ * normChar K t) u := fun ⟨u, h⟩ => hχ ⟨u + -t, by
      rw [isNormPow_iff] at h ⊢
      rw [normChar_add, ← h, mul_assoc, ← normChar_add, add_neg_cancel, normChar_zero, mul_one]⟩
    obtain ⟨Λ', h1, h2⟩ := exists_entire_ne_zero GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds
      (hu.mul (isUnitary_normChar t)) hχ'
    have h3 : IsHeckeL (χ * normChar K t) fun z => Λ (z + (t : ℂ) * Complex.I) :=
      ⟨hΛ.1.comp (by fun_prop), fun z hz => by
        rw [eulerFactor_mul_normChar]
        exact hΛ.2 _ (by simpa using hz)⟩
    have h4 := (isContAtOne_of_isHeckeL h3).apply_one_eq (isContAtOne_of_isHeckeL h1)
    rw [eq_one_add_of_re hs.symm]
    exact fun h => h2 (h4.symm.trans h)

theorem _root_.GlobalTheory.Published.HeckeLPartialContinuation_holds : GlobalTheory.Published.HeckeLPartialContinuation := by
  intro K _ _ T hT
  obtain ⟨T, rfl⟩ : ∃ T' : Finset _, (T' : Set _) = T := ⟨hT.toFinset, hT.coe_toFinset⟩
  refine ⟨fun χ hu hχ => ?_, ?_⟩
  · obtain ⟨Λ, hΛ⟩ := entire_of_not_normPow hu hχ
    exact ⟨fun s => Λ s * removed T χ s, hΛ.1.mul (differentiable_removed T χ),
      fun s hs => (heckeL_eq_mul_removed T hu hs (hΛ.2 s hs)).symm,
      fun s hs => mul_ne_zero (IsHeckeL.ne_zero_of_one_le hu hχ hΛ hs) (removed_ne_zero T hu (by linarith))⟩
  · obtain ⟨Z, hZd, hZ1, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero K
    have hu : (1 : HChar K).IsUnitary := fun _ => by simp
    have hc : ∀ P : HeightOneSpectrum (𝓞 K), cf (1 : HChar K) P = 1 := fun P => if_pos fun _ _ => rfl
    refine ⟨fun s => Z s * removed T 1 s, hZd.mul (differentiable_removed T 1), fun s hs => ?_,
      fun s hs => mul_ne_zero ?_ (removed_ne_zero T hu (by linarith))⟩
    · have h := hasProd_exp hu hs
      simp only [hc] at h
      beta_reduce
      rw [← heckeL_one, heckeL_eq_mul_removed T hu hs h, hZ s hs, mul_assoc]
    · rcases hs.lt_or_eq with hs | hs
      · rw [hZ s hs]
        exact mul_ne_zero (sub_ne_zero.2 fun h => by rw [h] at hs; simp at hs) (Complex.exp_ne_zero _)
      · rw [eq_one_add_of_re hs.symm]
        by_cases ht : s.im = 0
        · simpa [ht] using hZ1
        · exact GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I _ _ two_le_N sumN nonemptyN Z hZd hZ _ ht

end GlobalTheory.HeckePartial

end
