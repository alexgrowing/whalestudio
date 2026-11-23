import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem norm_cubN (h : N.Int q) (k : ℕ) (a b x : N.A) : ‖((cubN N.θ k a b x : Cˣ) : C)‖ = 1 := by
  rw [cubN, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun i _ => h.θ _ _ _

theorem norm_dbl (h : N.Int q) (x : N.A) : ‖((dbl N.θ N.σ x : Cˣ) : C)‖ = 1 := by
  rw [dbl, Units.val_div_eq_div_val, norm_div, h.θ, h.σ, div_one]

theorem norm_mulq (h : N.Int q) (n : ℕ) (x : N.A) : ‖((mulq N.θ N.σ n x : Cˣ) : C)‖ = 1 := by
  rw [mulq, Units.coe_prod, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Units.val_div_eq_div_val, norm_div, h.norm_cubN, Units.val_pow_eq_pow_val, norm_pow, h.norm_dbl,
    one_pow, div_one]

theorem norm_τ (h : N.Int q) (a b : N.X) : ‖(N.τ a b : C)‖ = Real.exp (-QuadraticMap.polar q a b) := by
  rw [NumD.τ, Units.val_div_eq_div_val, Units.val_div_eq_div_val, norm_div, norm_div, h.ψ, h.ψ, h.ψ,
    ← Real.exp_sub, ← Real.exp_sub, QuadraticMap.polar]
  congr 1
  ring

theorem norm_pow_generators_eq_pow (h : N.Int q) (g : N.Gt) (k : ℕ) (χ : N.X) :
    ‖((g ^ k).s χ : C)‖ = ‖(g.s χ : C)‖ ^ k := by
  have := congrArg (fun u : Cˣ => ‖(u : C)‖) (g.pow_s k χ)
  simpa only [Units.val_mul, norm_mul, h.norm_cubN, mul_one, Units.val_pow_eq_pow_val, norm_pow] using this

theorem norm_rep_generators_eq_exp (h : N.Int q) {k : ℕ} (p : N.QT k) (hk : k ≠ 0) (χ : N.X) :
    ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k)) := by
  have e := h.norm_pow_generators_eq_pow p.1.2 k χ
  rw [N.mem_QT.1 p.2, NumD.io_s, h.norm_τ] at e
  refine (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le hk).1 ?_
  rw [← e, ← Real.exp_nat_mul]
  congr 1
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  field_simp

theorem norm_wQ (h : N.Int q) {k : ℕ} (hk : Odd k) (p : N.QT k) :
    ‖(N.wQ p : C)‖ = Real.exp (-(q p.1.1.toAdd / k)) := by
  have hk0 : k ≠ 0 := hk.pos.ne'
  rw [NumD.wQ, NumB.wS]
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val, norm_div, norm_mul, norm_pow,
    h.norm_cubN, h.norm_dbl, h.norm_mulq, h.ψ, h.norm_rep_generators_eq_exp p hk0, mul_one, one_pow, div_one]
  rw [← Real.exp_nat_mul, ← Real.exp_sub, QuadraticMap.polar_self]
  congr 1
  obtain ⟨j, rfl⟩ := hk
  have e : (2 * j + 1 - 1) / 2 = j := by omega
  have : ((2 * j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  rw [e, two_smul]
  field_simp
  push_cast
  ring

theorem norm_txT (h : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  rw [NumD.txT, NumD.vt]
  simp only [Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, h.norm_mulq, h.ψ,
    h.norm_wQ hm.pow, h.norm_pow_generators_eq_pow, h.norm_rep_generators_eq_exp p (pow_ne_zero 2 hm0), div_one, NumD.Gt.pow_b]
  rw [← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  have e : q (p.1.1.toAdd + m • χ) =
      q p.1.1.toAdd + (m : ℝ) ^ 2 * q χ + m * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (m • χ) = m * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (m • χ) = (m : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm0
  rw [e]
  push_cast
  field_simp
  ring

end GlobalTheory.Ex.NumD.Int

namespace GlobalTheory.Ex

theorem norm_QT_s_and_norm_txT : ∀ (C : Type) [NormedField C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → (∀ (k : ℕ) (p : N.QT k), k ≠ 0 → ∀ χ, ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k))) ∧ ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) χ, ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ :=
  fun _ _ _ _ h => ⟨fun _ p hk χ => h.norm_rep_generators_eq_exp p hk χ, fun _ hm p χ => h.norm_txT hm p χ⟩
end GlobalTheory.Ex
