import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
open MvPolynomial GlobalTheory.ArInt GlobalTheory.Mean4O
open scoped Classical

namespace GlobalTheory.PolarNum

theorem lin_add_smul {κ : Type} [Fintype κ] (a b : κ → ℝ) (t : ℝ) :
    lin (b + t • a) = C t * lin a + lin b := by
  simp only [lin, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem num_cons_eq {e : ℕ} {M : Man e} (K : Calc M) {ι : Type} [Fintype ι] (v : ι → K.V) (w : K.V)
    (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ) (ν : ℝ) (hν : ν ≠ 0)
    (h : ∀ a : Option ι → ℝ,
      Φ (lin a ^ (e + 1)) = ν * K.top (∑ i, a (some i) • v i + a none • w))
    (α β : Option ι → ℝ) :
    K.num (Fin.cons (∑ i, α (some i) • v i + α none • w)
        fun _ => ∑ i, β (some i) • v i + β none • w) =
      Φ (lin α * lin β ^ e) / ν := by
  set x : K.V := ∑ i, β (some i) • v i + β none • w with hx
  set y : K.V := ∑ i, α (some i) • v i + α none • w with hy
  have hA : ∀ t : ℝ, ∑ i, (β + t • α) (some i) • v i + (β + t • α) none • w = x + t • y := by
    intro t
    simp only [hx, hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, smul_add, Finset.smul_sum]
    abel
  have hL : ∀ t : ℝ, Φ (lin (β + t • α) ^ (e + 1)) =
      ∑ m ∈ Finset.range (e + 1 + 1),
        (((e + 1).choose m : ℝ) * Φ (lin α ^ m * lin β ^ (e + 1 - m))) * t ^ m := by
    intro t
    rw [lin_add_smul, add_pow, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : (C t * lin α) ^ m * lin β ^ (e + 1 - m) * ((e + 1).choose m : MvPolynomial (Option ι) ℝ)
        = (((e + 1).choose m : ℝ) * t ^ m) • (lin α ^ m * lin β ^ (e + 1 - m)) := by
      rw [smul_eq_C_mul, map_mul, map_pow, map_natCast]
      ring
    rw [this, map_smul, smul_eq_mul]
    ring
  have key := GlobalTheory.PolarDeg.lin_coeff_eq (Finset.range (e + 1 + 1))
    (Finset.univ : Finset (Finset (Fin (e + 1))))
    (fun m => ((e + 1).choose m : ℝ) * Φ (lin α ^ m * lin β ^ (e + 1 - m))) (fun m => m)
    (fun s => ν * K.num (s.piecewise (fun _ => y) fun _ => x)) (fun s => s.card) (by
      intro t
      rw [← hL, h, hA, Calc.top, GlobalTheory.PolarDeg.num_expand K.num K.symm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring)
  have hR : (∑ s : Finset (Fin (e + 1)),
      if s.card = 1 then ν * K.num (s.piecewise (fun _ => y) fun _ => x) else 0) =
      ν * (((e : ℝ) + 1) * K.num (Fin.cons y fun _ => x)) := by
    rw [← GlobalTheory.PolarDeg.num_lin K.num K.symm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  rw [hR, Finset.sum_ite_eq' (Finset.range (e + 1 + 1)) 1, if_pos (by simp)] at key
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_one,
    Nat.add_sub_cancel] at key
  have he : (e : ℝ) + 1 ≠ 0 := by positivity
  rw [eq_div_iff hν]
  apply mul_left_cancel₀ he
  rw [key]
  ring

end GlobalTheory.PolarNum
