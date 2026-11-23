import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

namespace PolynomialFrame

theorem pow_mul_prod {k : ℕ} {s : ℂ} (hs : s ≠ 0) (a b : Fin k → ℂ) (m : Fin k →₀ ℕ) {d : ℕ}
    (hm : m.degree ≤ d) :
    s ^ d * ∏ i ∈ m.support, (a i + s⁻¹ * b i) ^ m i =
      s ^ (d - m.degree) * ∏ i ∈ m.support, (s * a i + b i) ^ m i := by
  calc s ^ d * ∏ i ∈ m.support, (a i + s⁻¹ * b i) ^ m i
      = s ^ (d - m.degree) * (s ^ m.degree * ∏ i ∈ m.support, (a i + s⁻¹ * b i) ^ m i) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
    _ = s ^ (d - m.degree) * ∏ i ∈ m.support, (s * a i + b i) ^ m i := by
        congr 1
        rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_pow]
        congr 1
        field_simp

theorem exists_eval_line_ne_zero {k : ℕ} (P : MvPolynomial (Fin k) ℂ) (v : Fin k → ℂ)
    (hv : eval v (homogeneousComponent P.totalDegree P) ≠ 0) (w : Fin k → ℂ) :
    ∃ t : ℂ, eval (w + t • v) P ≠ 0 := by
  by_contra! h
  set d := P.totalDegree with hd
  have hdeg : ∀ m ∈ P.support, m.degree ≤ d := fun m hm => le_totalDegree hm
  set H : ℂ → ℂ := fun s => ∑ m ∈ P.support,
    coeff m P * (s ^ (d - m.degree) * ∏ i ∈ m.support, (s * w i + v i) ^ m i) with hH
  have hHc : Continuous H := by
    simp only [hH]
    fun_prop
  have hzero : ∀ s : ℂ, s ≠ 0 → H s = 0 := by
    intro s hs
    have h1 := h s⁻¹
    rw [eval_eq] at h1
    have : H s = s ^ d * ∑ m ∈ P.support, coeff m P * ∏ i ∈ m.support, ((w + s⁻¹ • v) i) ^ m i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm (s ^ d), pow_mul_prod hs w v m (hdeg m hm)]
    rw [this, h1, mul_zero]
  have h0 : H 0 = 0 := by
    have h1 : Tendsto H (𝓝[≠] 0) (𝓝 (H 0)) := hHc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto H (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hzero s hs).symm)
    exact tendsto_nhds_unique h1 h2
  apply hv
  rw [homogeneousComponent_apply, map_sum, ← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [eval_monomial, Finsupp.prod]
  split_ifs with hmd
  · rw [hmd, Nat.sub_self, pow_zero, one_mul]
    simp
  · have : d - m.degree ≠ 0 := by have := hdeg m hm; omega
    rw [zero_pow this, zero_mul, mul_zero]

theorem homogeneousComponent_totalDegree_ne_zero {k : ℕ} {P : MvPolynomial (Fin k) ℂ} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  have hne : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hP)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup P.support hne (fun s => s.sum fun _ e => e)
  intro h0
  have h1 := congrArg (coeff m) h0
  rw [coeff_homogeneousComponent, coeff_zero, if_pos] at h1
  · exact (mem_support_iff.mp hm) h1
  · rw [totalDegree, hmax]
    rfl

end PolynomialFrame

open PolynomialFrame in

theorem exists_frame_lines_not_in_zeroSet {k : ℕ} {P : MvPolynomial (Fin k) ℂ} (hP : P ≠ 0) :
    ∃ M : Matrix (Fin k) (Fin k) ℂ, M.det ≠ 0 ∧
      ∀ (i : Fin k) (w : Fin k → ℂ), ∃ t : ℂ, eval (w + t • fun j => M j i) P ≠ 0 := by
  set Pd := homogeneousComponent P.totalDegree P
  have hPd : Pd ≠ 0 := homogeneousComponent_totalDegree_ne_zero hP
  set F : MvPolynomial (Fin k × Fin k) ℂ :=
    (Matrix.mvPolynomialX (Fin k) (Fin k) ℂ).det * ∏ i, rename (fun j => (j, i)) Pd
  have hF : F ≠ 0 := by
    refine mul_ne_zero (Matrix.det_mvPolynomialX_ne_zero _ _) (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    have hinj : Function.Injective (fun j : Fin k => (j, i)) := fun a b h => (Prod.ext_iff.mp h).1
    intro h
    exact hPd (rename_injective _ hinj (by rw [h, map_zero]))
  obtain ⟨s, hs⟩ : ∃ s : Fin k × Fin k → ℂ, eval s F ≠ 0 := by
    by_contra! hs
    exact hF (MvPolynomial.funext fun x => by rw [hs x, map_zero])
  refine ⟨Matrix.of fun i j => s (i, j), ?_, fun i w => exists_eval_line_ne_zero P _ ?_ w⟩
  · have h := hs
    rw [map_mul, Matrix.eval_det_mvPolynomialX] at h
    exact left_ne_zero_of_mul h
  · have h : eval s F ≠ 0 := hs
    rw [map_mul, map_prod] at h
    have h2 := (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)) i (Finset.mem_univ i)
    rw [eval_rename] at h2
    exact h2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
