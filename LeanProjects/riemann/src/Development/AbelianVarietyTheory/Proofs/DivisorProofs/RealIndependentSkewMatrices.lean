import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem linearIndependent_of_skew_of_real : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r n : ℕ} (G : Matrix (Fin r) (Fin r) E), G.det ≠ 0 →
    ∀ e : Fin n → Matrix (Fin r) (Fin r) E, (∀ i, (e i)ᵀ * G + G * (e i).map cc = 0) →
    LinearIndependent (maximalRealSubfield E) e → LinearIndependent E e := by
  intro E _ _ _ r n G hG e he hF
  have cc_mul' : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => map_mul (IsCMField.complexConj E) x y
  have cc_add' : ∀ x y : E, cc (x + y) = cc x + cc y := fun x y => map_add (IsCMField.complexConj E) x y
  have cc_cc' : ∀ x : E, cc (cc x) = x := fun x => IsCMField.complexConj_apply_apply E x

  have hmap : ∀ g : Fin n → E, (∑ i, g i • e i).map cc = ∑ i, cc (g i) • (e i).map cc := by
    intro g
    ext a b
    simp [Matrix.sum_apply, cc, map_sum]
  have hinj : ∀ M : Matrix (Fin r) (Fin r) E, Mᵀ * G = 0 → M = 0 := by
    intro M hM
    have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
    have h0 : Mᵀ = 0 := by
      have := congrArg (· * G⁻¹) hM
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv G hu] using this
    simpa using congrArg Matrix.transpose h0
  have key : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∑ i, cc (g i) • e i = 0 := by
    intro g hg
    apply hinj
    have h2 : G * (∑ i, g i • e i).map cc = 0 := by
      rw [hg]
      ext a b
      simp [Matrix.mul_apply, cc]
    rw [hmap, Finset.mul_sum] at h2
    have h3 : (∑ i, cc (g i) • e i)ᵀ * G = - ∑ i, G * (cc (g i) • (e i).map cc) := by
      rw [Matrix.transpose_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_neg]
      congr 1
      exact eq_neg_of_add_eq_zero_left (he i)
    rw [h3, h2, neg_zero]

  have real : ∀ g : Fin n → E, (∀ i, cc (g i) = g i) → ∑ i, g i • e i = 0 → ∀ i, g i = 0 := by
    intro g hc hg i
    have hm : ∀ i, g i ∈ maximalRealSubfield E := fun i =>
      (IsCMField.complexConj_eq_self_iff E _).mp (hc i)
    have := Fintype.linearIndependent_iff.mp hF (fun i => ⟨g i, hm i⟩) hg i
    simpa using congrArg (Subtype.val) this
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  have hx' : cc x ≠ x := hx

  have sum_real : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∀ i, g i + cc (g i) = 0 := by
    intro g hg
    apply real
    · intro i
      rw [cc_add', cc_cc', add_comm]
    · simp only [add_smul, Finset.sum_add_distrib, hg, key g hg, add_zero]
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := sum_real g hg i
  have hxg : ∑ i, (x * g i) • e i = 0 := by
    simp only [mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have h2 := sum_real (fun i => x * g i) hxg i
  simp only [cc_mul'] at h2
  have h3 : cc (g i) = - g i := eq_neg_of_add_eq_zero_right h1
  rw [h3] at h2
  have h4 : (x - cc x) * g i = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hx'
  · exact h

end GlobalTheory
