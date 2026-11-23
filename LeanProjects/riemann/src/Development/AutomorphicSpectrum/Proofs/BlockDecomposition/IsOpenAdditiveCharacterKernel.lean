import Mathlib

open Matrix Filter Topology ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalFieldChar

theorem circle_eq_one_of_forall_re_pow_pos (z : Circle)
    (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  have hsq : ∀ w : Circle, (w : ℂ).re ^ 2 + (w : ℂ).im ^ 2 = 1 := by
    intro w
    have := Circle.normSq_coe w
    rw [Complex.normSq_apply] at this
    nlinarith
  by_contra hz
  have ha0 : (z : ℂ).re < 1 := by
    by_contra hge
    push_neg at hge
    have h2 := hsq z
    have him : (z : ℂ).im = 0 := by nlinarith [sq_nonneg (z : ℂ).im, sq_nonneg ((z : ℂ).re - 1)]
    have hre : (z : ℂ).re = 1 := by
      rw [him] at h2
      nlinarith
    exact hz (Circle.ext (Complex.ext (by simpa using hre) (by simpa using him)))
  set a : ℕ → ℝ := fun j => ((z ^ (2 ^ j) : Circle) : ℂ).re with ha
  have hstep : ∀ j, a (j + 1) = 2 * a j ^ 2 - 1 := by
    intro j
    have h2 := hsq (z ^ (2 ^ j))
    have hp : z ^ (2 ^ (j + 1)) = z ^ (2 ^ j) * z ^ (2 ^ j) := by
      rw [pow_succ, pow_mul, sq]
    simp only [ha]
    rw [hp, Circle.coe_mul, Complex.mul_re]
    nlinarith
  have hlow : ∀ j, (2 : ℝ) ^ j * (1 - (z : ℂ).re) ≤ 1 - a j := by
    intro j
    induction j with
    | zero => simp [ha]
    | succ j ih =>
      have hpos : 0 < a j := h _
      have hle : a j ≤ 1 := by
        have := hsq (z ^ (2 ^ j))
        have h3 : a j ^ 2 ≤ 1 := by
          simp only [ha]
          nlinarith [sq_nonneg ((z ^ (2 ^ j) : Circle) : ℂ).im]
        nlinarith
      rw [hstep, pow_succ]
      nlinarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
  have hd : 0 < 1 - (z : ℂ).re := by linarith
  rw [div_lt_iff₀ hd] at hj
  have := hlow j
  have hpos : 0 < a j := h _
  linarith

theorem isOpen_addChar_ker : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    IsOpen {x : k | ψ x = 1} := by
  intro k _ _ _ _ ψ hψ
  let H : AddSubgroup k :=
    { carrier := {x | ψ x = 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [AddChar.map_neg_eq_inv, ha, inv_one] }
  have hV : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_induced_dom)
  have hU : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : k) :=
    (hV.preimage hψ).mem_nhds (by simp)
  obtain ⟨γ, hγ, hball⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 hU
  have hsmul : ∀ x : k, valuation k x < γ → ∀ n : ℕ, valuation k (n • x) < γ := by
    intro x hx n
    induction n with
    | zero => simpa using zero_lt_iff.2 hγ
    | succ n ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_lt _ ih hx
  have hone : ∀ x : k, valuation k x < γ → x ∈ H := by
    intro x hx
    refine circle_eq_one_of_forall_re_pow_pos (ψ x) fun n => ?_
    have h1 : 0 < ((ψ (n • x) : Circle) : ℂ).re := hball (hsmul x hx n)
    rwa [AddChar.map_nsmul_eq_pow] at h1
  have hnh : (H : Set k) ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨γ, hγ, fun x hx => hone x hx⟩
  exact H.isOpen_of_mem_nhds hnh

end GlobalTheory.CompanionTheory.LocalFieldChar
