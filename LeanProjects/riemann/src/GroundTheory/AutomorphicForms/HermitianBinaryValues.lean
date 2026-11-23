import Mathlib
import GroundTheory.AutomorphicForms.HermitianLocalSplit
import GroundTheory.GlobalFields.Adele.WeakApprox
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
import GroundTheory.GlobalFields.LocalFieldAtPlace

noncomputable section

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain GroundTheory.Global Filter

section Algebra

variable {K : Type*} [Field K]

theorem sq_two_omega_sub {γ t : K} :
    ((2 : QuadraticAlgebra K (-γ) t) * QuadraticAlgebra.omega - algebraMap K _ t) ^ 2 =
      algebraMap K _ (t ^ 2 - 4 * γ) := by
  ext <;> simp [sq, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

end Algebra

section Archimedean

open NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {v : InfinitePlace K}

theorem exists_sq_of_isComplex (hv : v.IsComplex) (x : v.Completion) : ∃ r, r ^ 2 = x := by
  set e := ringEquivComplexOfIsComplex hv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x) two_pos
  exact ⟨e.symm z, by rw [← map_pow, hz, RingEquiv.symm_apply_apply]⟩

theorem exists_sq_iff_of_isReal (hv : v.IsReal) (x : v.Completion) :
    (∃ r, r ^ 2 = x) ↔ 0 ≤ ringEquivRealOfIsReal hv x := by
  set e := ringEquivRealOfIsReal hv
  constructor
  · rintro ⟨r, rfl⟩
    rw [map_pow]
    positivity
  · intro h
    exact ⟨e.symm (Real.sqrt (e x)), by rw [← map_pow, Real.sq_sqrt h, e.symm_apply_apply]⟩

theorem continuous_ringEquivRealOfIsReal (hv : v.IsReal) :
    Continuous (ringEquivRealOfIsReal hv) := by
  have : (ringEquivRealOfIsReal hv : v.Completion → ℝ) = extensionEmbeddingOfIsReal hv := by
    ext x
    simp
  rw [this]
  exact (isometry_extensionEmbeddingOfIsReal hv).continuous

theorem neg_of_not_sqNorm_of_isReal (hv : v.IsReal) {d β : v.Completion} (hd : d ≠ 0)
    (h : ¬ SqNorm d β) :
    ringEquivRealOfIsReal hv d < 0 ∧ ringEquivRealOfIsReal hv β < 0 := by
  have h2 : (2 : v.Completion) ≠ 0 := by
    intro h0
    have := congrArg (ringEquivRealOfIsReal hv) h0
    rw [map_ofNat, map_zero] at this
    norm_num at this
  constructor
  · by_contra H
    push Not at H
    obtain ⟨r, hr⟩ := (exists_sq_iff_of_isReal hv d).2 H
    have hr0 : r ≠ 0 := by rintro rfl; exact hd (by rw [← hr]; ring)
    exact h (sqNorm_of_eq_sq h2 hr.symm hr0 β)
  · by_contra H
    push Not at H
    obtain ⟨r, hr⟩ := (exists_sq_iff_of_isReal hv β).2 H
    exact h (hr ▸ sqNorm_sq d r)

end Archimedean

section Main

open NumberField.InfinitePlace.Completion

universe u

variable {K : Type u} [Field K] [NumberField K]

section AtL

open scoped NumberField.LiesOver
open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

variable {γ t : K} [Fact (∀ r : K, r ^ 2 ≠ -γ + t * r)]

theorem sqNorm_finite_quadraticAlgebra {d β : K} (hd0 : d ≠ 0) (hβ : β ≠ 0)
    (w : HeightOneSpectrum (𝓞 (QuadraticAlgebra K (-γ) t)))
    (hgood : SqNorm (algebraMap K ((below K w).adicCompletion K) d) (algebraMap K _ β) ∨
      ∀ r : (below K w).adicCompletion K, r ^ 2 ≠ algebraMap K _ (t ^ 2 - 4 * γ)) :
    SqNorm (algebraMap (QuadraticAlgebra K (-γ) t) (w.adicCompletion (QuadraticAlgebra K (-γ) t))
        (algebraMap K (QuadraticAlgebra K (-γ) t) d))
      (algebraMap (QuadraticAlgebra K (-γ) t) (w.adicCompletion (QuadraticAlgebra K (-γ) t))
        (algebraMap K (QuadraticAlgebra K (-γ) t) β)) := by
  set v := below K w
  set φ := completionMap v w
  have hφ : ∀ x : K, φ (algebraMap K (v.adicCompletion K) x) =
      algebraMap (QuadraticAlgebra K (-γ) t) (w.adicCompletion (QuadraticAlgebra K (-γ) t))
        (algebraMap K (QuadraticAlgebra K (-γ) t) x) := by
    intro x
    rw [completionMap_algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [← hφ, ← hφ]
  rcases hgood with h | h
  · exact h.map φ
  · have : CharZero (v.adicCompletion K) :=
      charZero_of_injective_algebraMap (algebraMap K _).injective
    refine sqNorm_of_quadratic φ h (s := algebraMap (QuadraticAlgebra K (-γ) t) _
      ((2 : QuadraticAlgebra K (-γ) t) * QuadraticAlgebra.omega - algebraMap K _ t)) ?_
      ((map_ne_zero _).2 hd0) ((map_ne_zero _).2 hβ)
    rw [← map_pow, sq_two_omega_sub, hφ]

theorem sqNorm_infinite_quadraticAlgebra {d β : K} (hd0 : d ≠ 0) (hβ : β ≠ 0)
    (w : InfinitePlace (QuadraticAlgebra K (-γ) t))
    (hgood : SqNorm (algebraMap K (w.comap (algebraMap K (QuadraticAlgebra K (-γ) t))).Completion d)
        (algebraMap K _ β) ∨
      ∀ r : (w.comap (algebraMap K (QuadraticAlgebra K (-γ) t))).Completion,
        r ^ 2 ≠ algebraMap K _ (t ^ 2 - 4 * γ)) :
    SqNorm (algebraMap (QuadraticAlgebra K (-γ) t) w.Completion
        (algebraMap K (QuadraticAlgebra K (-γ) t) d))
      (algebraMap (QuadraticAlgebra K (-γ) t) w.Completion
        (algebraMap K (QuadraticAlgebra K (-γ) t) β)) := by
  set v := w.comap (algebraMap K (QuadraticAlgebra K (-γ) t))
  have : w.LiesOver v := (InfinitePlace.liesOver_iff_comap_eq v w).2 rfl
  set φ := algebraMap v.Completion w.Completion
  have hφ : ∀ x : K, φ (algebraMap K v.Completion x) =
      algebraMap (QuadraticAlgebra K (-γ) t) w.Completion
        (algebraMap K (QuadraticAlgebra K (-γ) t) x) := by
    intro x
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [← hφ, ← hφ]
  by_cases hS : SqNorm (algebraMap K v.Completion d) (algebraMap K _ β)
  · exact hS.map φ
  have hns := hgood.resolve_left hS
  have hv : v.IsReal := by
    rcases v.isReal_or_isComplex with h | h
    · exact h
    · exact absurd (exists_sq_of_isComplex h _) (by push Not; exact hns)
  set e := ringEquivRealOfIsReal hv
  have hβv := (neg_of_not_sqNorm_of_isReal hv ((map_ne_zero _).2 hd0) hS).2
  have hev : e (algebraMap K v.Completion (t ^ 2 - 4 * γ)) < 0 := by
    by_contra H
    push Not at H
    obtain ⟨r, hr⟩ := (exists_sq_iff_of_isReal hv _).2 H
    exact hns r hr
  obtain ⟨q, hq⟩ := (exists_sq_iff_of_isReal hv
    (algebraMap K v.Completion β / algebraMap K v.Completion (t ^ 2 - 4 * γ))).2
    (by rw [map_div₀]; exact (div_pos_of_neg_of_neg hβv hev).le)
  have hne : algebraMap K v.Completion (t ^ 2 - 4 * γ) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hev
    exact lt_irrefl _ hev
  refine ⟨algebraMap (QuadraticAlgebra K (-γ) t) w.Completion
    ((2 : QuadraticAlgebra K (-γ) t) * QuadraticAlgebra.omega - algebraMap K _ t) * φ q, 0, ?_⟩
  rw [mul_pow, ← map_pow, sq_two_omega_sub, ← hφ, ← map_pow, ← map_mul, hq,
    mul_div_cancel₀ _ hne]
  ring

end AtL

end Main

end GroundTheory.Automorphic
