import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShNums

theorem pow_six_le_exp {eps : ℝ} (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 4 ≤ x ∧ x ^ 6 ≤ Real.exp (x ^ (eps / 3)) := by
  have h := (isLittleO_log_rpow_atTop (r := eps / 3) (by positivity)).bound (c := 1 / 6) (by norm_num)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop (4 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  have hx' : 0 < x := by linarith
  refine ⟨h2, ?_⟩
  have hp : 0 < x ^ (eps / 3) := Real.rpow_pos_of_pos hx' _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at h1
  have h3 : Real.log x ≤ 1 / 6 * x ^ (eps / 3) := (le_abs_self _).trans h1
  calc x ^ 6 = Real.exp (Real.log (x ^ 6)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      rw [Real.log_pow]
      push_cast
      linarith

theorem size_rel_at {D : D7} (L : SizeData₂ D) (hs : SizesAt L) (h4 : 4 ≤ L.sc.x) (h6 : L.sc.x ^ 6 ≤ L.sc.X') :
    (D.R.k : ℝ) * D.R.N D.R.m ≤ L.Sc / 4 ∧ (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧ L.etaSz ≤ L.sc.w'' D.R.n ∧
    L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x ∧ 4 ≤ L.sc.x ∧ 2 * L.sc.b' ≤ L.sc.b ∧
    (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b ∧ 1 ≤ L.sc.w'' D.R.n ∧ L.etaSz + 1 + 3 * L.Sc ≤ L.sc.b := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, hEta, -, -, hDel, hW, -⟩ := hs
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hm : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by
      unfold Ranks.n
      exact D.R.ord_pos
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    refine le_trans (Real.one_le_rpow hx1 ?_) hK.1
    unfold szTh
    linarith
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := by
    refine hK.2.trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    unfold szTh
    push_cast
    linarith
  have hb1 : 1 ≤ L.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_le_exp (by positivity)
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hb' : L.sc.b' * L.sc.X' = L.sc.x * L.sc.b := by
    unfold Scale.b' Scale.a
    field_simp
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a
    positivity
  have h5b : L.sc.x ^ 5 * L.sc.b' ≤ L.sc.b := by
    have : L.sc.x * (L.sc.x ^ 5 * L.sc.b') ≤ L.sc.x * L.sc.b := by
      rw [← hb']
      calc L.sc.x * (L.sc.x ^ 5 * L.sc.b') = L.sc.b' * L.sc.x ^ 6 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h6 hb'0.le
    exact le_of_mul_le_mul_left this hx0
  have hx5 : (4 : ℝ) ^ 5 ≤ L.sc.x ^ 5 := pow_le_pow_left₀ (by norm_num) h4 5
  have h5b' : 5 * L.sc.b' ≤ L.sc.b := by nlinarith
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    apply div_le_div_of_nonneg_left hb'0.le hx0
    nlinarith
  have hw' : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1
  have hw1 : 1 ≤ L.sc.w'' D.R.n := le_trans (Real.one_le_sqrt.2 hb1) hW
  have heta0 := L.etaSz_pos
  have hS0 := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have heta : L.etaSz ≤ L.sc.w'' D.R.n := by
    refine le_trans ?_ hEta.2.2.2.2.1
    apply le_mul_of_one_le_left heta0.le
    nlinarith
  have hS : L.Sc ≤ L.sc.w'' D.R.n := le_trans (le_mul_of_one_le_left hS0.le hk1) hDel.2.2.2.1
  have hN : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) :=
    le_trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hm)) hDel.1
  refine ⟨?_, hDel.2.2.2.1, hEta.2.2.2.2.1, heta, hw, h4, by linarith, ?_, hw1, by linarith⟩
  · rw [L.Sc_eq]
    have := mul_le_mul_of_nonneg_left hN (le_trans zero_le_one hk1)
    linarith
  · exact le_trans (mul_le_mul_of_nonneg_right hk5 hb'0.le) h5b

theorem size_rel : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m ≤ (Fm.L x i).Sc / 4 ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ ((Fm.D x i).R.m : ℝ) * (((Fm.D x i).R.t : ℝ) + 1) * (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.b' / (Fm.L x i).sc.x ∧ 4 ≤ (Fm.L x i).sc.x ∧ 2 * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc ≤ (Fm.L x i).sc.b := by
  intro eps Fm
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := pow_six_le_exp he
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨h4, h6⟩ := hx0 x hx
  apply size_rel_at (Fm.L x i) (Fm.sizes x hx1 i)
  · rw [Fm.L_x x i hx1]; exact h4
  · unfold Scale.X'
    rw [Fm.L_x x i hx1, Fm.L_eps x i]; exact h6

end GlobalTheory.ShNums
