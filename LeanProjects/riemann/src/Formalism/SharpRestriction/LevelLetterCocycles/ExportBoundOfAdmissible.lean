import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallSum

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

open Classical in
theorem sum_small (T : Finset ℕ) (hT : ∀ l ∈ T, l.Prime ∧ l ≠ 2 ∧ l ≠ 3 ∧ (l : ℝ) ≤ lStar L) :
    ∑ l ∈ T, Real.log l * (bbB L C + lenB L C l) ≤ 1000 * (C + 1) ^ 3 * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
  have h5 : ∀ l ∈ T, 5 ≤ l := fun l hl => ge_five (hT l hl).1 (hT l hl).2.1 (hT l hl).2.2.1
  have hT1 : ∀ l ∈ T, 1 ≤ l ∧ (l : ℝ) ≤ lStar L := fun l hl => ⟨by have := h5 l hl; omega, (hT l hl).2.2.2⟩
  have hT2 : ∀ l ∈ T, 2 ≤ l ∧ (l : ℝ) ≤ lStar L := fun l hl => ⟨by have := h5 l hl; omega, (hT l hl).2.2.2⟩
  have hbb := sum_bb L hC P hPar hL T hT1
  have hep := sum_eP L hC P hPar hL T hT1
  have hb := sum_rowb L hC P hPar hL (T.filter (cB L)) (fun l hl => by
    obtain ⟨hlT, hc⟩ := Finset.mem_filter.1 hl
    exact ⟨h5 l hlT, hc.2.1⟩)
  have hc := sum_rowc L hC P hPar hL (T.filter (cC L)) (fun l hl => (Finset.mem_filter.1 hl).2.2.2)
  have hd := sum_rowd L hC P hPar hL (T.filter (cD L)) (fun l hl => by
    obtain ⟨hlT, hcd⟩ := Finset.mem_filter.1 hl
    refine ⟨by have := h5 l hlT; omega, (hT l hlT).1.odd_of_ne_two (hT l hlT).2.1, ?_⟩
    by_contra ho
    push_neg at ho
    exact hcd.2.1 ⟨hcd.2.2, ho⟩)
  have hfl := sum_flat L hC P hPar hL T hT2
  have hpt : ∀ l ∈ T, Real.log l * (bbB L C + lenB L C l) ≤ Real.log l * bbB L C +
      ((3 + 2 * C) * D.R.f * D.R.m * (C * (Real.log l + hB L * (Real.log l / l) + Real.log (hB L))) +
      (if cB L l then 4 * D.R.f * C * D.R.r * (Real.log l * rowBr L l) else 0) +
      (if cC L l then 4 * D.R.f * C * D.R.r * hB L * (Real.log l / (l : ℝ) ^ 2) else 0) +
      (if cD L l then 4 * D.R.f * C * D.R.r * hB L * (Real.log l / (l : ℝ) ^ 2) else 0) +
      4 * D.R.f * C * D.R.r * (Real.log l * flatB L C l)) := by
    intro l hl
    have := lenB_split L hC (show 2 ≤ l by have := h5 l hl; omega)
    rw [mul_add]
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum]
  have hm := m_ge_one D
  have hb1 := one_le_b L
  have hL1 := L_ge_one L
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  set X := (D.R.f : ℝ) * D.R.m * L.sc.b * large₂ L ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hLL : large₂ L ≤ large₂ L ^ 2 := by nlinarith
  have e1 : C * D.R.f * D.R.m * L.sc.b * large₂ L ≤ C * X := by
    rw [hX]; have : 0 ≤ C * D.R.f * D.R.m * L.sc.b := by positivity
    nlinarith
  have e2 : (3 + 2 * C) * D.R.f * D.R.m * (C * ∑ l ∈ T, (Real.log l + hB L * (Real.log l / l) + Real.log (hB L))) ≤
      11 * C * (3 + 2 * C) * X := by
    rw [hX]
    have : 0 ≤ (3 + 2 * C) * D.R.f * D.R.m * C := by positivity
    calc (3 + 2 * C) * D.R.f * D.R.m * (C * ∑ l ∈ T, (Real.log l + hB L * (Real.log l / l) + Real.log (hB L)))
        = ((3 + 2 * C) * D.R.f * D.R.m * C) * ∑ l ∈ T, (Real.log l + hB L * (Real.log l / l) + Real.log (hB L)) := by ring
      _ ≤ ((3 + 2 * C) * D.R.f * D.R.m * C) * (11 * L.sc.b * large₂ L ^ 2) := mul_le_mul_of_nonneg_left hep this
      _ = _ := by ring
  have hXb : 80 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 = 80 * C * X := by rw [hX]; ring
  have hXc : 64 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 = 64 * C * X := by rw [hX]; ring
  have hXd : 32 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 = 32 * C * X := by rw [hX]; ring
  have hXf : 4 * C * (102 + 4 * (2 * C + 1) ^ 2) * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 =
      4 * C * (102 + 4 * (2 * C + 1) ^ 2) * X := by rw [hX]; ring
  have hK : C + 11 * C * (3 + 2 * C) + 80 * C + 64 * C + 32 * C + 4 * C * (102 + 4 * (2 * C + 1) ^ 2) ≤
      1000 * (C + 1) ^ 3 := by nlinarith
  have hfin : 1000 * (C + 1) ^ 3 * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 = 1000 * (C + 1) ^ 3 * X := by rw [hX]; ring
  rw [hfin]
  have : (C + 11 * C * (3 + 2 * C) + 80 * C + 64 * C + 32 * C + 4 * C * (102 + 4 * (2 * C + 1) ^ 2)) * X ≤
      1000 * (C + 1) ^ 3 * X := mul_le_mul_of_nonneg_right hK hX0
  have e1' : ∑ l ∈ T, Real.log l * bbB L C ≤ C * X := hbb.trans e1
  linarith

end Sums

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

def Ub (C : ℝ) : ℝ := L.sc.x ^ (C + 2) * Real.exp (L.sc.x ^ (L.sc.eps / 4))

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem xC_le_U : L.sc.x ^ C ≤ Ub L C := by
  have hx : (1:ℝ) ≤ L.sc.x := le_trans (by norm_num) hL.x100
  have h2 : (1:ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have h3 : L.sc.x ^ C ≤ L.sc.x ^ (C + 2) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h4 : 0 ≤ L.sc.x ^ (C + 2) := Real.rpow_nonneg (by linarith) _
  unfold Ub
  exact le_trans h3 (le_mul_of_one_le_right h4 h2)

theorem one_le_U : 1 ≤ Ub L C := by
  have hx : (1:ℝ) ≤ L.sc.x := le_trans (by norm_num) hL.x100
  have h1 : (1:ℝ) ≤ L.sc.x ^ (C + 2) := Real.one_le_rpow hx (by linarith)
  have h2 : (1:ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  unfold Ub
  exact one_le_mul_of_one_le_of_one_le h1 h2

theorem x_le_U : L.sc.x ≤ Ub L C := by
  have hx : (1:ℝ) ≤ L.sc.x := le_trans (by norm_num) hL.x100
  have h2 : (1:ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have h3 : L.sc.x ^ (1:ℝ) ≤ L.sc.x ^ (C + 2) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  rw [Real.rpow_one] at h3
  have h4 : 0 ≤ L.sc.x ^ (C + 2) := Real.rpow_nonneg (by linarith) _
  unfold Ub
  exact le_trans h3 (le_mul_of_one_le_right h4 h2)

theorem E_le_U : Real.exp (L.sc.x ^ (L.sc.eps / 4)) ≤ Ub L C := by
  have hx : (1:ℝ) ≤ L.sc.x := le_trans (by norm_num) hL.x100
  have h1 : (1:ℝ) ≤ L.sc.x ^ (C + 2) := Real.one_le_rpow hx (by linarith)
  unfold Ub
  exact le_mul_of_one_le_left (Real.exp_pos _).le h1

theorem eta_le_U : L.etaSz ≤ Ub L C := by
  have h := P.logeta
  have := Real.exp_log L.etaSz_pos
  have : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := by
    rw [← Real.exp_log L.etaSz_pos]; exact Real.exp_le_exp.2 h
  exact this.trans (E_le_U L hC P hPar hL)

theorem S_le_U : L.Sc ≤ 4 * Ub L C := by
  have hS := L.Sc_eq
  have hSp := L.Sc_pos
  have hk : (0 : ℝ) < D.R.k := by linarith [k_ge_five D]
  have hDel : 0 < (D.s.Del : ℝ) := by
    by_contra h; push_neg at h
    have : L.Sc ≤ 0 := by rw [hS]; nlinarith
    linarith
  have h := P.logDel
  have hxe : 0 ≤ L.sc.x ^ (L.sc.eps / 4) := Real.rpow_nonneg (x_pos L).le _
  have hD : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := by
    rw [← Real.exp_log hDel]; exact Real.exp_le_exp.2 (by linarith)
  have hkx : (D.R.k : ℝ) ≤ L.sc.x ^ C := hPar.2.2.1
  rw [hS]
  unfold Ub
  have h1 : L.sc.x ^ C ≤ L.sc.x ^ (C + 2) := Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith)
  have : (D.R.k : ℝ) * (D.s.Del : ℝ) ≤ L.sc.x ^ (C + 2) * Real.exp (L.sc.x ^ (L.sc.eps / 4)) :=
    mul_le_mul (hkx.trans h1) hD hDel.le (Real.rpow_nonneg (x_pos L).le _)
  linarith

theorem ranks_le_U : (D.R.n : ℝ) ≤ Ub L C ∧ (D.R.k : ℝ) ≤ Ub L C ∧ (D.R.t : ℝ) ≤ Ub L C ∧
    (D.R.m : ℝ) ≤ Ub L C ∧ (D.R.f : ℝ) ≤ 2 * Ub L C ∧ (D.R.r : ℝ) ≤ 2 * Ub L C ∧
    (D.R.N D.R.m : ℝ) + D.R.t ≤ 4 * Ub L C ^ 2 ∧ (D.R.nV : ℝ) ≤ 4 * Ub L C ^ 2 := by
  have hP' := hPar
  unfold ParametersPolynomiallyBounded at hP'
  obtain ⟨-, -, hk, hn, ht, -, -, -⟩ := hP'
  have hU := xC_le_U L hC P hPar hL
  have hU1 := one_le_U L hC P hPar hL
  have hkU : (D.R.k : ℝ) ≤ Ub L C := le_trans hk hU
  have hnU : (D.R.n : ℝ) ≤ Ub L C := le_trans hn hU
  have htU : (D.R.t : ℝ) ≤ Ub L C := le_trans ht hU
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hmU : (D.R.m : ℝ) ≤ Ub L C := le_trans (by exact_mod_cast hmk) hkU
  have hrk : D.R.r ≤ 2 * D.R.k := by show D.R.k + D.R.m - 1 ≤ 2 * D.R.k; omega
  have hrU : (D.R.r : ℝ) ≤ 2 * Ub L C := by
    have : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast hrk
    linarith
  have hfU : (D.R.f : ℝ) ≤ 2 * Ub L C := by
    have : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by exact_mod_cast (show D.R.f = 2 * D.R.n from rfl)
    linarith
  have hN : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by
    exact_mod_cast (show D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) from rfl)
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by
    exact_mod_cast (show D.R.nV = D.R.r + D.R.t from rfl)
  have hm0 : (0:ℝ) ≤ D.R.m := by positivity
  have ht0 : (0:ℝ) ≤ D.R.t := by positivity
  have hU0 : (0:ℝ) ≤ Ub L C := by linarith
  have hmt : (D.R.m : ℝ) * (D.R.t + 1) ≤ Ub L C * (Ub L C + 1) :=
    mul_le_mul hmU (by linarith) (by linarith) hU0
  have hUU : Ub L C * 1 ≤ Ub L C * Ub L C := mul_le_mul_of_nonneg_left hU1 hU0
  refine ⟨hnU, hkU, htU, hmU, hfU, hrU, ?_, ?_⟩
  · rw [hN]; nlinarith
  · rw [hnV]; nlinarith

theorem Den_le_U : Den L ≤ 10 * Ub L C ^ 7 := by
  obtain ⟨hn, hk, ht, -, -, -, hNt, -⟩ := ranks_le_U L hC P hPar hL
  have hS := S_le_U L hC P hPar hL
  have hU1 := one_le_U L hC P hPar hL
  have hxU := x_le_U L hC P hPar hL
  have hx1 : (1:ℝ) ≤ L.sc.x := le_trans (by norm_num) hL.x100
  have hLg : large₂ L ≤ Ub L C := by
    have h : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [L.sc.eps_lt])
    rw [Real.rpow_one] at h
    exact le_trans h hxU
  have hLg0 : 0 ≤ large₂ L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hS0 : 0 ≤ L.Sc := L.Sc_pos.le
  have hU0 : (0:ℝ) ≤ Ub L C := by linarith
  have ht0 : (0:ℝ) ≤ D.R.t := by positivity
  have hB0 : 0 ≤ L.Sc + D.R.t + large₂ L := by linarith
  have hA : (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂ L ^ 2 ≤
      Ub L C * Ub L C ^ 2 * (4 * Ub L C ^ 2) * Ub L C ^ 2 := by
    gcongr <;> first | assumption | positivity | linarith
  have hB : (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L) ≤
      Ub L C * Ub L C ^ 2 * (4 * Ub L C + Ub L C + Ub L C) := by
    gcongr <;> first | assumption | positivity | linarith
  have h47 : Ub L C ^ 4 ≤ Ub L C ^ 7 := pow_le_pow_right₀ hU1 (by norm_num)
  unfold Den
  nlinarith

end Sums

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

private theorem sc_b_ge_const_mul_Ub_pow_eighteen : 4 * 10 ^ 6 * (C + 1) ^ 2 * Ub L C ^ 18 ≤ L.sc.b := by
  have hx1 : (1:ℝ) ≤ L.sc.x := le_trans (by norm_num) hL.x100
  have hx0 : (0:ℝ) < L.sc.x := by linarith
  have hA : (C + 1) ^ 2 ≤ (C + 1) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (C + 1)) hC.le]
  have hx2 : 4 * 10 ^ 6 * (C + 1) ^ 2 ≤ L.sc.x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL.x100 hx0.le, hL.xK, hA, sq_nonneg (C + 1)]
  have hxp : L.sc.x ^ 2 ≤ L.sc.x ^ (2 * C + 4) := by
    rw [← Real.rpow_two L.sc.x]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hUb : Ub L C ^ 18 = L.sc.x ^ ((C + 2) * 18) * Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)) := by
    unfold Ub
    rw [mul_pow, ← Real.rpow_mul_natCast hx0.le, ← Real.exp_nat_mul]
    norm_num
  have hkey := hL.ex
  have hsplit1 : L.sc.x ^ (20 * C + 40) = L.sc.x ^ ((C + 2) * 18) * L.sc.x ^ (2 * C + 4) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hsplit2 : Real.exp (20 * L.sc.x ^ (L.sc.eps / 4)) =
      Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)) * Real.exp (2 * L.sc.x ^ (L.sc.eps / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit1, hsplit2] at hkey
  have h1 : (1:ℝ) ≤ L.sc.x ^ (C + 2) := Real.one_le_rpow hx1 (by linarith)
  have hE2 : (1:ℝ) ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 4)) :=
    Real.one_le_exp (mul_nonneg (by norm_num) (Real.rpow_nonneg hx0.le _))
  have hP : 0 ≤ L.sc.x ^ ((C + 2) * 18) := Real.rpow_nonneg hx0.le _
  have hQ : 0 ≤ Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)) := (Real.exp_pos _).le
  have hR : 4 * 10 ^ 6 * (C + 1) ^ 2 ≤ L.sc.x ^ (2 * C + 4) := le_trans hx2 hxp
  have hX0 : 0 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := (Real.exp_pos _).le
  show 4 * 10 ^ 6 * (C + 1) ^ 2 * Ub L C ^ 18 ≤ Real.exp (L.sc.x ^ L.sc.eps)
  rw [hUb]
  calc 4 * 10 ^ 6 * (C + 1) ^ 2 * (L.sc.x ^ ((C + 2) * 18) * Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)))
      ≤ L.sc.x ^ (2 * C + 4) * (L.sc.x ^ ((C + 2) * 18) * Real.exp (18 * L.sc.x ^ (L.sc.eps / 4))) :=
        mul_le_mul_of_nonneg_right hR (mul_nonneg hP hQ)
    _ ≤ L.sc.x ^ (2 * C + 4) * (L.sc.x ^ ((C + 2) * 18) * Real.exp (18 * L.sc.x ^ (L.sc.eps / 4))) *
          Real.exp (2 * L.sc.x ^ (L.sc.eps / 4)) :=
        le_mul_of_one_le_right (mul_nonneg (Real.rpow_nonneg hx0.le _) (mul_nonneg hP hQ)) hE2
    _ = L.sc.x ^ ((C + 2) * 18) * L.sc.x ^ (2 * C + 4) *
          (Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)) * Real.exp (2 * L.sc.x ^ (L.sc.eps / 4))) := by ring
    _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := hkey
    _ ≤ L.sc.x ^ (C + 2) * Real.exp (L.sc.x ^ (L.sc.eps / 3)) := le_mul_of_one_le_left hX0 h1
    _ ≤ Real.exp (L.sc.x ^ L.sc.eps) := hL.Xb

theorem lA_lt_lStar : lA L < lStar L := by
  have hP' := hPar
  unfold ParametersPolynomiallyBounded at hP'
  obtain ⟨-, -, hk, -, -, hde, -, -⟩ := hP'
  have hU1 := one_le_U L hC P hPar hL
  have hxU := x_le_U L hC P hPar hL
  have hCU := xC_le_U L hC P hPar hL
  have hDen := Den_le_U L hC P hPar hL
  have hb := sc_b_ge_const_mul_Ub_pow_eighteen L hC P hPar hL
  have hx1 : (1:ℝ) ≤ L.sc.x := le_trans (by norm_num) hL.x100
  have hx0 : (0:ℝ) < L.sc.x := by linarith
  have hxe : L.sc.x ^ L.sc.eps ≤ Ub L C := by
    have h : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [L.sc.eps_lt])
    rw [Real.rpow_one] at h; exact le_trans h hxU
  have hxe0 : 0 < L.sc.x ^ L.sc.eps := Real.rpow_pos_of_pos hx0 _
  have hxe0' : 0 ≤ L.sc.x ^ L.sc.eps := hxe0.le
  have hinv : L.sc.x ^ (-L.sc.eps) * L.sc.x ^ L.sc.eps = 1 := by
    rw [← Real.rpow_add hx0]; simp
  have hde1 : 1 ≤ L.de2 * L.sc.x ^ L.sc.eps := by
    nlinarith [mul_le_mul_of_nonneg_right hde hxe0.le]
  have hm2 : (2:ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hde0 : 0 < L.de2 := L.thickDensity_pos
  have hk0 : (0:ℝ) ≤ D.R.k := by positivity
  have hkU : (D.R.k : ℝ) ≤ Ub L C := le_trans hk hCU
  have hU0 : (0:ℝ) ≤ Ub L C := by linarith
  have hA : lA L ≤ Ub L C ^ 3 := by
    show (D.R.k : ℝ) * L.sc.x ^ L.sc.eps / ((D.R.m : ℝ) * L.de2) ≤ Ub L C ^ 3
    rw [div_le_iff₀ (by positivity)]
    have h1 : (D.R.k : ℝ) * L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps ≤ Ub L C ^ 3 := by
      calc (D.R.k : ℝ) * L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps ≤ Ub L C * Ub L C * Ub L C := by
            gcongr <;> first | assumption | positivity | linarith
        _ = Ub L C ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_right h1 hde0.le,
      mul_le_mul_of_nonneg_left hde1 (mul_nonneg hk0 hxe0.le),
      mul_le_mul_of_nonneg_left hm2 (mul_nonneg (pow_nonneg hU0 3) hde0.le),
      mul_nonneg (pow_nonneg hU0 3) hde0.le]
  have hDen0 : 0 < Den L := by
    have hn1 : (1:ℝ) ≤ D.R.n := by
      have h1 := D.R.two_le_m
      have h2 := D.R.m_le_f
      have : 1 ≤ D.R.n := by show 1 ≤ D.R.ord; omega
      exact_mod_cast this
    have hk1 : (1:ℝ) ≤ D.R.k := by
      have h1 := D.R.m_add_three_le_k
      have : 1 ≤ D.R.k := by omega
      exact_mod_cast this
    have hS0 := L.Sc_pos
    have ht0 : (0:ℝ) ≤ D.R.t := by positivity
    have hLg0 : 0 ≤ large₂ L := by show 0 ≤ L.sc.x ^ L.sc.eps; exact hxe0'
    have hA0 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂ L ^ 2 := by
      positivity
    have hB0 : 0 < (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L) :=
      mul_pos (mul_pos (by linarith) (pow_pos (by linarith) 2)) (by linarith)
    unfold Den; linarith
  have hLs : lStar L = (D.R.m : ℝ) * L.sc.b / Den L := rfl
  have hlow : Ub L C ^ 3 < lStar L := by
    rw [hLs, lt_div_iff₀ hDen0]
    have h1C : (1:ℝ) ≤ (C + 1) ^ 2 := by nlinarith
    have hU18 : 0 < Ub L C ^ 18 := pow_pos (by linarith) 18
    have h1018 : Ub L C ^ 10 ≤ Ub L C ^ 18 := pow_le_pow_right₀ hU1 (by norm_num)
    have hb0 : 0 ≤ L.sc.b := le_trans (by positivity) hb
    nlinarith [mul_le_mul_of_nonneg_left hDen (pow_nonneg hU0 3),
      mul_le_mul_of_nonneg_right h1C hU18.le, mul_le_mul_of_nonneg_right hm2 hb0]
  exact lt_of_le_of_lt hA hlow

set_option maxHeartbeats 1000000 in
theorem exc_pt {l : ℕ} (hl : lStar L < l) :
    bbB L C + lenB L C l ≤ 1000 * (C + 1) ^ 2 * Ub L C ^ 9 := by
  have hls := seven_lt_lStar L P
  have hl8 : (8 : ℝ) ≤ l := by
    have : 7 < (l : ℝ) := by linarith
    have : 7 < l := by exact_mod_cast this
    exact_mod_cast (show 8 ≤ l by omega)
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hn, hk, ht, hm, hf, hr, hNt, hnV⟩ := ranks_le_U L hC P hPar hL
  have hU1 := one_le_U L hC P hPar hL
  set U := Ub L C with hUdef
  have hDen := Den_le_U L hC P hPar hL
  have hbD := b_div_lStar L
  have hh := hB_le L hC P hPar hL
  have hh1 := one_le_hB L
  have hls0 := lStar_pos L
  have hLg := (log_le_x L hC P hPar hL).trans (x_le_U L hC P hPar hL)
  have hL0 := Lg_nonneg L
  have hb1 := one_le_b L

  have hhl : hB L / l ≤ 2 * Den L := by
    calc hB L / l ≤ hB L / lStar L := div_le_div_of_nonneg_left (by linarith) hls0 hl.le
      _ ≤ 2 * L.sc.b / lStar L := by gcongr
      _ = 2 * (L.sc.b / lStar L) := by ring
      _ ≤ 2 * Den L := by linarith

  have hlog1 : 1 ≤ Real.log (l : ℝ) := by
    have : Real.exp 1 ≤ (l : ℝ) := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  have hlogh : Real.log (hB L) ≤ large₂ L + 1 := by
    have := Real.log_le_log (by linarith) hh
    rw [Real.log_mul (by norm_num) (by linarith), b_eq, Real.log_exp] at this
    have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hlb : Real.logb l (hB L) ≤ large₂ L + 1 := by
    unfold Real.logb
    have h0 : 0 ≤ Real.log (hB L) := Real.log_nonneg hh1
    exact (div_le_self h0 hlog1).trans hlogh
  have hU7 : U ≤ U ^ 7 := by
    calc U = U ^ 1 := (pow_one U).symm
      _ ≤ U ^ 7 := pow_le_pow_right₀ hU1 (by norm_num)
  have hU79 : U ^ 7 * U ^ 2 = U ^ 9 := by ring
  have hePl : eP L C l ≤ C * (23 * U ^ 7) := by
    unfold eP
    apply mul_le_mul_of_nonneg_left _ hC.le
    have : (1 : ℝ) ≤ U ^ 7 := one_le_pow₀ hU1
    linarith
  have he0 := eP_nonneg L hC.le l

  have hbb : bbB L C ≤ 8 * C * U ^ 9 := by
    unfold bbB
    have h1 : (D.R.f : ℝ) * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * large₂ L ^ 2 ≤ (2 * U) * U * U ^ 2 * (4 * U ^ 2) * U ^ 2 := by
      gcongr
    have h2 : (2 * U) * U * U ^ 2 * (4 * U ^ 2) * U ^ 2 ≤ 8 * U ^ 9 := by
      have : U ^ 8 ≤ U ^ 9 := pow_le_pow_right₀ hU1 (by norm_num)
      nlinarith
    calc C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * large₂ L ^ 2
        = C * ((D.R.f : ℝ) * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * large₂ L ^ 2) := by ring
      _ ≤ C * (8 * U ^ 9) := mul_le_mul_of_nonneg_left (h1.trans h2) hC.le
      _ = 8 * C * U ^ 9 := by ring
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have hm0 : (0 : ℝ) ≤ D.R.m := by positivity
  have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
  have hlen : lenB L C l ≤ (754 * C + 92 * C ^ 2) * U ^ 9 := by
    unfold lenB
    by_cases hs : SplitK D l
    · rw [if_pos hs]
      have : (2 * (D.R.f : ℝ) * D.R.m + D.R.f) ≤ 6 * U ^ 2 := by
        have : (D.R.f : ℝ) * D.R.m ≤ (2 * U) * U := mul_le_mul hf hm hm0 (by linarith)
        nlinarith
      calc (2 * (D.R.f : ℝ) * D.R.m + D.R.f) * eP L C l ≤ (6 * U ^ 2) * (C * (23 * U ^ 7)) :=
            mul_le_mul this hePl he0 (by positivity)
        _ = 138 * C * (U ^ 7 * U ^ 2) := by ring
        _ ≤ (754 * C + 92 * C ^ 2) * U ^ 9 := by
            rw [hU79]
            have h9 : 0 ≤ U ^ 9 := by positivity
            have : 138 * C ≤ 754 * C + 92 * C ^ 2 := by nlinarith only [hC]
            exact mul_le_mul_of_nonneg_right this h9
    · rw [if_neg hs]
      have hnb : ¬ ((l : ℝ) < lA L ∧ 4 * D.host.Lw < ordH D l) := by
        intro h; have := lA_lt_lStar L hC P hPar hL; linarith [h.1]
      rw [if_neg hnb]
      have hq : hB L / (l : ℝ) ^ 2 ≤ 20 * U ^ 7 := by
        have : hB L / (l : ℝ) ^ 2 ≤ hB L / l := by
          apply div_le_div_of_nonneg_left (by linarith only [hh1]) hl0
          rw [sq]; exact le_mul_of_one_le_left hl0.le (by linarith only [hl8])
        linarith only [this, hhl, hDen]
      have hfl : flatB L C l ≤ 18 * U ^ 7 := by
        unfold flatB
        have hwe := placeWeight_add_eta_le L P
        have hb'l : L.sc.b' < l := (lStar_gt L P).trans hl
        have h1 : (wP L + eta₃ L) / l ≤ 9 := by
          rw [div_le_iff₀ hl0]; linarith
        have hI : bandI L C l ≤ 1 := by unfold bandI; split_ifs <;> norm_num
        have hI0 := bandI_nonneg L C l
        have he4 := etaP_le L P
        have heU := eta_le_U L hC P hPar hL
        have hSU := S_le_U L hC P hPar hL
        have h2 : eta₃ L * bandI L C l ≤ 4 * U := by
          have := etaP_nonneg L
          calc eta₃ L * bandI L C l ≤ eta₃ L * 1 := mul_le_mul_of_nonneg_left hI this
            _ ≤ 4 * U := by linarith only [he4, heU]
        have h7 : (1 : ℝ) ≤ U ^ 7 := one_le_pow₀ hU1
        linarith only [h1, h2, hSU, hLg, hU7, h7]
      have hA : 4 * (D.R.f : ℝ) * (C * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l)) ≤ 608 * C * U ^ 9 := by
        have h1 : (D.R.f : ℝ) * D.R.r ≤ (2 * U) * (2 * U) := mul_le_mul hf hr hr0 (by linarith)
        have h2 : hB L / (l : ℝ) ^ 2 + flatB L C l ≤ 38 * U ^ 7 := by linarith only [hq, hfl]
        have h3 : 0 ≤ hB L / (l : ℝ) ^ 2 + flatB L C l := by
          have := flatB_nonneg L C l; have : 0 ≤ hB L / (l : ℝ) ^ 2 := by positivity
          linarith
        calc 4 * (D.R.f : ℝ) * (C * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l))
            = 4 * C * ((D.R.f : ℝ) * D.R.r) * (hB L / (l : ℝ) ^ 2 + flatB L C l) := by ring
          _ ≤ 4 * C * ((2 * U) * (2 * U)) * (38 * U ^ 7) := by gcongr
          _ = 608 * C * (U ^ 7 * U ^ 2) := by ring
          _ = 608 * C * U ^ 9 := by rw [hU79]
      have hB2 : 2 * (D.R.f : ℝ) * (C * D.R.m * eP L C l) ≤ 92 * C ^ 2 * U ^ 9 := by
        have h1 : (D.R.f : ℝ) * D.R.m ≤ (2 * U) * U := mul_le_mul hf hm hm0 (by linarith)
        calc 2 * (D.R.f : ℝ) * (C * D.R.m * eP L C l) = 2 * C * ((D.R.f : ℝ) * D.R.m) * eP L C l := by ring
          _ ≤ 2 * C * ((2 * U) * U) * (C * (23 * U ^ 7)) := by gcongr
          _ = 92 * C ^ 2 * (U ^ 7 * U ^ 2) := by ring
          _ = 92 * C ^ 2 * U ^ 9 := by rw [hU79]
      have h9 : 0 ≤ U ^ 9 := by positivity
      have : (608 * C) * U ^ 9 + 92 * C ^ 2 * U ^ 9 ≤ (754 * C + 92 * C ^ 2) * U ^ 9 := by
        have : 0 ≤ 146 * C * U ^ 9 := by positivity
        linarith only [this]
      linarith only [this, hA, hB2]
  have hU9 : 0 ≤ U ^ 9 := by positivity
  have : 8 * C * U ^ 9 + (754 * C + 92 * C ^ 2) * U ^ 9 ≤ 1000 * (C + 1) ^ 2 * U ^ 9 := by
    have h1 : 8 * C + (754 * C + 92 * C ^ 2) ≤ 1000 * (C + 1) ^ 2 := by nlinarith only [hC]
    have := mul_le_mul_of_nonneg_right h1 hU9
    linarith only [this]
  linarith only [this, hbb, hlen]

end Sums

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem big_le_b : 4 * 10 ^ 6 * (C + 1) ^ 2 * Ub L C ^ 18 ≤ L.sc.b := by
  have hx1 : (1:ℝ) ≤ L.sc.x := le_trans (by norm_num) hL.x100
  have hx0 : (0:ℝ) < L.sc.x := by linarith
  have hA : (C + 1) ^ 2 ≤ (C + 1) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (C + 1)) hC.le]
  have hx2 : 4 * 10 ^ 6 * (C + 1) ^ 2 ≤ L.sc.x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL.x100 hx0.le, hL.xK, hA, sq_nonneg (C + 1)]
  have hxp : L.sc.x ^ 2 ≤ L.sc.x ^ (2 * C + 4) := by
    rw [← Real.rpow_two L.sc.x]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hUb : Ub L C ^ 18 = L.sc.x ^ ((C + 2) * 18) * Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)) := by
    unfold Ub
    rw [mul_pow, ← Real.rpow_mul_natCast hx0.le, ← Real.exp_nat_mul]
    norm_num
  have hkey := hL.ex
  have hsplit1 : L.sc.x ^ (20 * C + 40) = L.sc.x ^ ((C + 2) * 18) * L.sc.x ^ (2 * C + 4) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hsplit2 : Real.exp (20 * L.sc.x ^ (L.sc.eps / 4)) =
      Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)) * Real.exp (2 * L.sc.x ^ (L.sc.eps / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit1, hsplit2] at hkey
  have h1 : (1:ℝ) ≤ L.sc.x ^ (C + 2) := Real.one_le_rpow hx1 (by linarith)
  have hE2 : (1:ℝ) ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 4)) :=
    Real.one_le_exp (mul_nonneg (by norm_num) (Real.rpow_nonneg hx0.le _))
  have hP : 0 ≤ L.sc.x ^ ((C + 2) * 18) := Real.rpow_nonneg hx0.le _
  have hQ : 0 ≤ Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)) := (Real.exp_pos _).le
  have hR : 4 * 10 ^ 6 * (C + 1) ^ 2 ≤ L.sc.x ^ (2 * C + 4) := le_trans hx2 hxp
  have hX0 : 0 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := (Real.exp_pos _).le
  show 4 * 10 ^ 6 * (C + 1) ^ 2 * Ub L C ^ 18 ≤ Real.exp (L.sc.x ^ L.sc.eps)
  rw [hUb]
  calc 4 * 10 ^ 6 * (C + 1) ^ 2 * (L.sc.x ^ ((C + 2) * 18) * Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)))
      ≤ L.sc.x ^ (2 * C + 4) * (L.sc.x ^ ((C + 2) * 18) * Real.exp (18 * L.sc.x ^ (L.sc.eps / 4))) :=
        mul_le_mul_of_nonneg_right hR (mul_nonneg hP hQ)
    _ ≤ L.sc.x ^ (2 * C + 4) * (L.sc.x ^ ((C + 2) * 18) * Real.exp (18 * L.sc.x ^ (L.sc.eps / 4))) *
          Real.exp (2 * L.sc.x ^ (L.sc.eps / 4)) :=
        le_mul_of_one_le_right (mul_nonneg (Real.rpow_nonneg hx0.le _) (mul_nonneg hP hQ)) hE2
    _ = L.sc.x ^ ((C + 2) * 18) * L.sc.x ^ (2 * C + 4) *
          (Real.exp (18 * L.sc.x ^ (L.sc.eps / 4)) * Real.exp (2 * L.sc.x ^ (L.sc.eps / 4))) := by ring
    _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := hkey
    _ ≤ L.sc.x ^ (C + 2) * Real.exp (L.sc.x ^ (L.sc.eps / 3)) := le_mul_of_one_le_left hX0 h1
    _ ≤ Real.exp (L.sc.x ^ L.sc.eps) := hL.Xb

end Sums

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

theorem lenB_nonneg {C : ℝ} (hC : 0 < C) {l : ℕ} (hl : 2 ≤ l) : 0 ≤ lenB L C l := by
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have hm0 : (0 : ℝ) ≤ D.R.m := by positivity
  have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
  have he := eP_nonneg L hC.le l
  have := rowBr_nonneg L hl
  have := flatB_nonneg L C l
  have hh : 0 ≤ hB L / (l : ℝ) ^ 2 := div_nonneg (by linarith [one_le_hB L]) (by positivity)
  unfold lenB
  split_ifs <;> positivity

theorem bbB_nonneg {C : ℝ} (hC : 0 < C) : 0 ≤ bbB L C := by
  unfold bbB
  apply mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le ?_) ?_) ?_) ?_) ?_ <;> positivity

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem card_exc_le (tb : Tab L) (hE : LargePrimeLengthVanishing L tb) : (tb.exc.card : ℝ) ≤ 388 * Ub L C ^ 8 := by
  have h := hE.2
  obtain ⟨hn, -, ht, -, -, -, -, -⟩ := ranks_le_U L hC P hPar hL
  have hU1 := one_le_U L hC P hPar hL
  set U := Ub L C
  have hTT : (D.host.TT.card : ℝ) ≤ 2 * U := by
    have h1 := P.TT_card_le
    have : LevelStarExponents.Nstar L ≤ 2 * D.R.n := by
      unfold LevelStarExponents.Nstar Scale.delta1
      have : L.sc.x ^ (-(L.sc.eps / 8)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos L.sc.one_lt_alt.le (by linarith [L.sc.eps_pos])
      have : (0 : ℝ) ≤ D.R.n := by positivity
      nlinarith
    linarith
  have hb8 : 8 * L.sc.b / lStar L ≤ 80 * U ^ 7 := by
    have := b_div_lStar L
    have := Den_le_U L hC P hPar hL
    rw [mul_div_assoc]; linarith
  have hS := S_le_U L hC P hPar hL
  have he := eta_le_U L hC P hPar hL
  have h7 : U ≤ U ^ 7 := by
    calc U = U ^ 1 := (pow_one U).symm
      _ ≤ U ^ 7 := pow_le_pow_right₀ hU1 (by norm_num)
  have h71 : (1 : ℝ) ≤ U ^ 7 := one_le_pow₀ hU1
  have hA : (D.host.TT.card : ℝ) + 2 ≤ 4 * U := by linarith
  have hB : L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 9 ≤ 97 * U ^ 7 := by linarith
  have hB0 : 0 ≤ L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 9 := by
    have := L.Sc_pos; have := L.etaSz_pos
    have : 0 ≤ 8 * L.sc.b / lStar L := div_nonneg (by linarith [one_le_b L]) (lStar_pos L).le
    have : (0 : ℝ) ≤ D.R.t := by positivity
    linarith
  calc (tb.exc.card : ℝ) ≤ ((D.host.TT.card : ℝ) + 2) * (L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 9) := h
    _ ≤ (4 * U) * (97 * U ^ 7) := mul_le_mul hA hB hB0 (by linarith)
    _ = 388 * U ^ 8 := by ring

theorem sum_exc (tb : Tab L) (hE : LargePrimeLengthVanishing L tb) (hX : ExceptionalPrimesBounded L tb) (T : Finset ℕ)
    (hT : ∀ l ∈ T, l ∈ tb.exc ∧ lStar L < l) :
    ∑ l ∈ T, Real.log l * (bbB L C + lenB L C l) ≤ 1164000 * (C + 1) ^ 2 * Ub L C ^ 18 := by
  have hU1 := one_le_U L hC P hPar hL
  set U := Ub L C with hUdef
  have hLg := (log_le_x L hC P hPar hL).trans (x_le_U L hC P hPar hL)
  have hls := seven_lt_lStar L P
  have hpt : ∀ l ∈ T, Real.log l * (bbB L C + lenB L C l) ≤ 3000 * (C + 1) ^ 2 * U ^ 10 := by
    intro l hl
    obtain ⟨hle, hlt⟩ := hT l hl
    have hl2 : 2 ≤ l := by
      have : (7 : ℝ) < l := by linarith
      have : 7 < l := by exact_mod_cast this
      omega
    have h3b := hX l hle
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
    have hlog : Real.log l ≤ 3 * U := by
      have := Real.log_le_log hl0 h3b
      rw [Real.log_mul (by norm_num) (by linarith [one_le_b L]), b_eq, Real.log_exp] at this
      have : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
      linarith
    have hg := exc_pt L hC P hPar hL hlt
    have hg0 : 0 ≤ bbB L C + lenB L C l := by
      have := bbB_nonneg L hC; have := lenB_nonneg L hC hl2; linarith
    calc Real.log l * (bbB L C + lenB L C l) ≤ (3 * U) * (1000 * (C + 1) ^ 2 * U ^ 9) :=
          mul_le_mul hlog hg hg0 (by linarith)
      _ = 3000 * (C + 1) ^ 2 * U ^ 10 := by ring
  have hsub : T ⊆ tb.exc := fun l hl => (hT l hl).1
  have hcard : (T.card : ℝ) ≤ 388 * U ^ 8 := by
    have := Finset.card_le_card hsub
    have : (T.card : ℝ) ≤ tb.exc.card := by exact_mod_cast this
    linarith [card_exc_le L hC P hPar hL tb hE]
  calc ∑ l ∈ T, Real.log l * (bbB L C + lenB L C l) ≤ T.card • (3000 * (C + 1) ^ 2 * U ^ 10) :=
        Finset.sum_le_card_nsmul _ _ _ hpt
    _ = (T.card : ℝ) * (3000 * (C + 1) ^ 2 * U ^ 10) := by rw [nsmul_eq_mul]
    _ ≤ (388 * U ^ 8) * (3000 * (C + 1) ^ 2 * U ^ 10) := by
        apply mul_le_mul_of_nonneg_right hcard; positivity
    _ = 1164000 * (C + 1) ^ 2 * U ^ 18 := by ring

theorem sum_g (T : Finset ℕ) (hT : ∀ l ∈ T, l ∈ gset D) :
    ∑ l ∈ T, Real.log l * (C * L.sc.x ^ C * L.etaSz) ≤ 2 * (C + 1) ^ 2 * Ub L C ^ 18 := by
  have hU1 := one_le_U L hC P hPar hL
  set U := Ub L C with hUdef
  have hLg := (log_le_x L hC P hPar hL).trans (x_le_U L hC P hPar hL)
  obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
  have hY0 : 0 < Y := by
    have : 0 < ((D.R.k : ℝ) * L.sc.b) ^ 8 := by
      have := k_ge_five D; have := one_le_b L; positivity
    linarith
  have hCYL := hPar.2.1
  have hxC := xC_le_U L hC P hPar hL
  have he := eta_le_U L hC P hPar hL
  have hpt : ∀ l ∈ T, Real.log l * (C * L.sc.x ^ C * L.etaSz) ≤ (C + 1) ^ 2 * U ^ 3 := by
    intro l hl
    have hlg := hT l hl
    have hlog : Real.log l ≤ (C + 1) * U := by
      have hgl : ∀ i, Real.log (D.host.g i) ≤ (C + 1) * U := by
        intro i
        obtain ⟨h1, h2⟩ := hY4 i
        have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le hY0 h1
        have := Real.log_le_log hg0 h2
        rw [Real.log_mul (by norm_num) hY0.ne'] at this
        have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
        have : P.CYL * large₂ L ≤ C * large₂ L := mul_le_mul_of_nonneg_right hCYL (Lg_nonneg L)
        have hY3' : Real.log Y ≤ P.CYL * large₂ L := hY3
        nlinarith
      unfold gset at hlg
      rcases Finset.mem_insert.1 hlg with h | h
      · rw [h]; exact hgl 0
      · rw [Finset.mem_singleton.1 h]; exact hgl 1
    have h0 : 0 ≤ C * L.sc.x ^ C * L.etaSz := by
      have := Real.rpow_nonneg (x_pos L).le C; have := L.etaSz_pos; positivity
    have h1 : C * L.sc.x ^ C * L.etaSz ≤ (C + 1) * U ^ 2 := by
      have : L.sc.x ^ C * L.etaSz ≤ U * U := mul_le_mul hxC he L.etaSz_pos.le (by linarith)
      calc C * L.sc.x ^ C * L.etaSz = C * (L.sc.x ^ C * L.etaSz) := by ring
        _ ≤ (C + 1) * (U * U) := mul_le_mul (by linarith) this
            (mul_nonneg (Real.rpow_nonneg (x_pos L).le C) L.etaSz_pos.le) (by linarith)
        _ = (C + 1) * U ^ 2 := by ring
    calc Real.log l * (C * L.sc.x ^ C * L.etaSz) ≤ ((C + 1) * U) * ((C + 1) * U ^ 2) :=
          mul_le_mul hlog h1 h0 (mul_nonneg (by linarith) (by linarith))
      _ = (C + 1) ^ 2 * U ^ 3 := by ring
  have hcard : (T.card : ℝ) ≤ 2 := by
    have : T ⊆ gset D := hT
    have h1 := Finset.card_le_card this
    have h2 : (gset D).card ≤ 2 := by unfold gset; exact Finset.card_le_two
    exact_mod_cast h1.trans h2
  have hU3 : U ^ 3 ≤ U ^ 18 := pow_le_pow_right₀ hU1 (by norm_num)
  calc ∑ l ∈ T, Real.log l * (C * L.sc.x ^ C * L.etaSz) ≤ T.card • ((C + 1) ^ 2 * U ^ 3) :=
        Finset.sum_le_card_nsmul _ _ _ hpt
    _ = (T.card : ℝ) * ((C + 1) ^ 2 * U ^ 3) := by rw [nsmul_eq_mul]
    _ ≤ 2 * ((C + 1) ^ 2 * U ^ 18) := by
        apply mul_le_mul hcard _ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_left hU3 (by positivity)
    _ = 2 * (C + 1) ^ 2 * U ^ 18 := by ring

end Sums

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem U_pow_eighteen_le_b : Ub L C ^ 18 ≤ L.sc.b := by
  have hU : 1 ≤ Ub L C := one_le_U L hC P hPar hL
  have hb := big_le_b L hC P hPar hL
  have hU18 : 0 ≤ Ub L C ^ 18 := by positivity
  have hK : (1:ℝ) ≤ 4 * 10 ^ 6 * (C + 1) ^ 2 := by nlinarith [hC]
  exact le_trans (le_mul_of_one_le_left hU18 hK) hb

theorem sum_23 (T : Finset ℕ) (hT : ∀ l ∈ T, l ∈ D.host.small ∨ l = 3) :
    ∑ l ∈ T, Real.log l * (C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * (large₂ L) ^ 2) ≤
      8 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
  have hm := m_ge_one D
  have hf1 : (1 : ℝ) ≤ D.R.f := (m_ge_one D).trans (m_le_f D)
  have hfm : (1 : ℝ) ≤ D.R.f * D.R.m := by nlinarith
  have hU1 := one_le_U L hC P hPar hL
  have hb : L.sc.x ^ C * large₂ L ≤ L.sc.b := by
    have h1 := xC_le_U L hC P hPar hL
    have h2 := (log_le_x L hC P hPar hL).trans (x_le_U L hC P hPar hL)
    have h3 : L.sc.x ^ C * large₂ L ≤ Ub L C * Ub L C := mul_le_mul h1 h2 (Lg_nonneg L) (by linarith)
    have h4 : Ub L C ^ 2 ≤ Ub L C ^ 18 := pow_le_pow_right₀ hU1 (by norm_num)
    have := U_pow_eighteen_le_b L hC P hPar hL
    nlinarith
  have h := UpperTheory.SmallSum.sum_row_small_le (L := large₂ L) (fm := (D.R.f : ℝ) * D.R.m) D.host.QS_pos.ne' D.host.QS_le
    L.sc.one_lt_alt.le hC (n_le L hC P hPar hL) hL.lg hb hfm T hT
  calc _ = ∑ l ∈ T, Real.log l * (C * ((D.R.f : ℝ) * D.R.m) * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * large₂ L ^ 2) :=
        Finset.sum_congr rfl fun l _ => by ring
    _ ≤ _ := h
    _ = _ := by ring

theorem log_qd_le : Real.log D.host.q ≤ large₂ L ∧ Real.log D.host.d ≤ large₂ L := by
  have h := P.condE_le
  have hq := P.qd_pow
  have hx0 : 0 ≤ L.sc.x ^ (2 * L.Ct + 5) := Real.rpow_nonneg (x_pos L).le _
  have hq0 : (0 : ℝ) < D.host.q := lt_of_le_of_lt hx0 hq.1
  have hd0 : (0 : ℝ) < D.host.d := lt_of_le_of_lt hx0 hq.2
  have hq1 : (1 : ℝ) ≤ D.host.q := by
    have : 0 < D.host.q := by exact_mod_cast hq0
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ D.host.d := by
    have : 0 < D.host.d := by exact_mod_cast hd0
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hc : (LevelStarExponents.condE D : ℝ) = D.host.QS * D.host.q * D.host.d := by unfold LevelStarExponents.condE; push_cast; ring
  have hnd : (1 : ℝ) ≤ D.host.QS * D.host.d := by
    have := one_le_mul_of_one_le_of_one_le hn hd1; linarith
  have hnq : (1 : ℝ) ≤ D.host.QS * D.host.q := by
    have := one_le_mul_of_one_le_of_one_le hn hq1; linarith
  have hcq : (D.host.q : ℝ) ≤ LevelStarExponents.condE D := by
    rw [hc, show (D.host.QS : ℝ) * D.host.q * D.host.d = D.host.q * (D.host.QS * D.host.d) by ring]
    exact le_mul_of_one_le_right (by linarith) hnd
  have hcd : (D.host.d : ℝ) ≤ LevelStarExponents.condE D := by
    rw [hc, show (D.host.QS : ℝ) * D.host.q * D.host.d = D.host.d * (D.host.QS * D.host.q) by ring]
    exact le_mul_of_one_le_right (by linarith) hnq
  have hc1 : (1 : ℝ) ≤ LevelStarExponents.condE D := hq1.trans hcq
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ (t_ge_one D)
  have hb := one_le_b L
  have hc36 : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := by
    calc (LevelStarExponents.condE D : ℝ) = (LevelStarExponents.condE D : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := pow_le_pow_right₀ hc1 (by norm_num)
  have hsq : L.sc.b ^ ((1 : ℝ) / 2) ≤ L.sc.b := by
    calc L.sc.b ^ ((1 : ℝ) / 2) ≤ L.sc.b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
      _ = L.sc.b := Real.rpow_one _
  have hcb : (LevelStarExponents.condE D : ℝ) ≤ L.sc.b := by
    have : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) ht
    linarith
  have hlb : Real.log L.sc.b = large₂ L := by rw [b_eq, Real.log_exp]
  constructor
  · calc Real.log D.host.q ≤ Real.log L.sc.b := Real.log_le_log hq0 (hcq.trans hcb)
      _ = large₂ L := hlb
  · calc Real.log D.host.d ≤ Real.log L.sc.b := Real.log_le_log hd0 (hcd.trans hcb)
      _ = large₂ L := hlb

theorem sum_qd (T : Finset ℕ) (hT : ∀ l ∈ T, l = D.host.q ∨ l = D.host.d) :
    ∑ l ∈ T, Real.log l * (2 * C * D.R.f * D.R.m * L.sc.b) ≤ 4 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
  have hqd := log_qd_le L hC P hPar hL
  have hL1 := L_ge_one L
  have hb := one_le_b L
  have h0 : 0 ≤ 2 * C * D.R.f * D.R.m * L.sc.b := by positivity
  have hpt : ∀ l ∈ T, Real.log l * (2 * C * D.R.f * D.R.m * L.sc.b) ≤ large₂ L * (2 * C * D.R.f * D.R.m * L.sc.b) := by
    intro l hl
    apply mul_le_mul_of_nonneg_right _ h0
    rcases hT l hl with h | h <;> rw [h]
    · exact hqd.1
    · exact hqd.2
  have hcard : (T.card : ℝ) ≤ 2 := by
    have h1 : T ⊆ {D.host.q, D.host.d} := fun l hl => by
      rcases hT l hl with h | h <;> simp [h]
    have := Finset.card_le_card h1
    have h2 : ({D.host.q, D.host.d} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    exact_mod_cast this.trans h2
  have hLL : large₂ L ≤ large₂ L ^ 2 := by nlinarith
  calc ∑ l ∈ T, Real.log l * (2 * C * D.R.f * D.R.m * L.sc.b) ≤ T.card • (large₂ L * (2 * C * D.R.f * D.R.m * L.sc.b)) :=
        Finset.sum_le_card_nsmul _ _ _ hpt
    _ = (T.card : ℝ) * (large₂ L * (2 * C * D.R.f * D.R.m * L.sc.b)) := by rw [nsmul_eq_mul]
    _ ≤ 2 * (large₂ L ^ 2 * (2 * C * D.R.f * D.R.m * L.sc.b)) := by
        apply mul_le_mul hcard _ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_right hLL h0
    _ = 4 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by ring

theorem glob_le :
    6 + UpperTheory.KStar.nuBudget D + Real.log (Formalism.MainNotions.N.hE D.host : ℝ) + Real.log (D.what₂.restRowsFiniteGroupCard : ℝ) ≤ 20 * (C + 1) ^ 2 * Ub L C ^ 18 := by
  have hnu : UpperTheory.KStar.nuBudget D ≤ 12 * (C + 1) ^ 2 * Ub L C ^ 18 := by
    obtain ⟨hn, -, ht, -, -, hr, -, -⟩ := ranks_le_U L hC P hPar hL
    have hb := UpperTheory.KStar.nuBudget_le D
    have a1 := Real.log_le_self (Nat.cast_nonneg (α := ℝ) D.R.n)
    have a2 := Real.log_le_self (Nat.cast_nonneg (α := ℝ) D.R.t)
    have a3 := Real.log_le_self (Nat.cast_nonneg (α := ℝ) D.R.r)
    have hU1 := one_le_U L hC P hPar hL
    have hU2 : Ub L C ≤ Ub L C ^ 18 := le_self_pow₀ hU1 (by norm_num)
    have hC1 : (1 : ℝ) ≤ (C + 1) ^ 2 := by nlinarith
    have h18 : Ub L C ^ 18 ≤ (C + 1) ^ 2 * Ub L C ^ 18 := le_mul_of_one_le_left (by positivity) hC1
    linarith
  have h1 := hPar.2.2.2.2.2.2.1
  have h2 := hPar.2.2.2.2.2.2.2
  have hU1 := one_le_U L hC P hPar hL
  have hxC := xC_le_U L hC P hPar hL
  have hLg := (log_le_x L hC P hPar hL).trans (x_le_U L hC P hPar hL)
  set U := Ub L C
  have hxC0 : 0 ≤ L.sc.x ^ C := Real.rpow_nonneg (x_pos L).le C
  have e1 : C * L.sc.x ^ C ≤ C * U := mul_le_mul_of_nonneg_left hxC hC.le
  have e2 : C * L.sc.x ^ C * large₂ L ≤ C * U * U := by
    have := Lg_nonneg L
    calc C * L.sc.x ^ C * large₂ L ≤ C * U * U := by gcongr
      _ = _ := rfl
  have hU2 : U ≤ U ^ 18 := by
    calc U = U ^ 1 := (pow_one U).symm
      _ ≤ U ^ 18 := pow_le_pow_right₀ hU1 (by norm_num)
  have hU3 : U * U ≤ U ^ 18 := by
    calc U * U = U ^ 2 := by ring
      _ ≤ U ^ 18 := pow_le_pow_right₀ hU1 (by norm_num)
  have h18 : 1 ≤ U ^ 18 := one_le_pow₀ hU1
  have hC1 : (1 : ℝ) ≤ (C + 1) ^ 2 := by nlinarith
  have : 6 + C * U + C * U * U ≤ 8 * (C + 1) ^ 2 * U ^ 18 := by
    have a1 : C * U ≤ (C + 1) ^ 2 * U ^ 18 := by
      have : C ≤ (C + 1) ^ 2 := by nlinarith
      exact mul_le_mul this hU2 (by linarith) (by positivity)
    have a2 : C * U * U ≤ (C + 1) ^ 2 * U ^ 18 := by
      have : C ≤ (C + 1) ^ 2 := by nlinarith
      calc C * U * U = C * (U * U) := by ring
        _ ≤ (C + 1) ^ 2 * U ^ 18 := mul_le_mul this hU3 (by positivity) (by positivity)
    have a3 : 6 ≤ 6 * ((C + 1) ^ 2 * U ^ 18) := by
      have : 1 ≤ (C + 1) ^ 2 * U ^ 18 := by nlinarith
      linarith
    linarith
  linarith

end Sums

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Point

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

set_option maxHeartbeats 1000000 in
open Classical in
theorem point_bound (tb : Tab L) (hA : AdmT L tb C P) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    6 + UpperTheory.KStar.nuBudget D + Real.log (Formalism.MainNotions.N.hE D.host : ℝ) + Real.log (D.what₂.restRowsFiniteGroupCard : ℝ) +
      ∑ l ∈ S, Real.log l * lamG L tb C l ≤ 2000 * (C + 1) ^ 3 * (D.R.f * D.R.m * L.sc.b * large₂ L ^ 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hRe, hExc, -, -, -, -⟩ := hA
  have hlog0 : ∀ l : ℕ, 0 ≤ Real.log (l : ℝ) := fun l => Real.log_natCast_nonneg l
  have hRf0 : 0 ≤ C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * (large₂ L) ^ 2 := by
    have := Real.log_nonneg L.sc.one_lt_alt.le; have := one_le_b L
    have := Real.rpow_nonneg (x_pos L).le C; positivity
  have hG0 : 0 ≤ C * L.sc.x ^ C * L.etaSz := by
    have := Real.rpow_nonneg (x_pos L).le C; have := L.etaSz_pos; positivity
  have hqd0 : 0 ≤ 2 * C * D.R.f * D.R.m * L.sc.b := by have := one_le_b L; positivity
  have hbb0 := bbB_nonneg L hC (C := C)
  have hpt : ∀ l ∈ S, Real.log l * lamG L tb C l ≤
      (if l ∈ gset D then Real.log l * (C * L.sc.x ^ C * L.etaSz) else 0) +
      (if l ∈ D.host.small ∨ l = 3 then Real.log l * (C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * (large₂ L) ^ 2) else 0) +
      (if l = D.host.q ∨ l = D.host.d then Real.log l * (2 * C * D.R.f * D.R.m * L.sc.b) else 0) +
      (if l ≠ 2 ∧ l ≠ 3 ∧ (l : ℝ) ≤ lStar L then Real.log l * (bbB L C + lenB L C l) else 0) +
      (if l ∈ tb.exc ∧ lStar L < l then Real.log l * (bbB L C + lenB L C l) else 0) := by
    intro l hl
    have hp := hS l hl
    have hl2 := hp.two_le
    have hlen0 := lenB_nonneg L hC hl2 (C := C)
    have a1 : 0 ≤ (if l ∈ gset D then Real.log l * (C * L.sc.x ^ C * L.etaSz) else 0) := by
      split_ifs; exact mul_nonneg (hlog0 l) hG0; exact le_rfl
    have a2 : 0 ≤ (if l ∈ D.host.small ∨ l = 3 then Real.log l * (C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * (large₂ L) ^ 2) else 0) := by
      split_ifs; exact mul_nonneg (hlog0 l) hRf0; exact le_rfl
    have a3 : 0 ≤ (if l = D.host.q ∨ l = D.host.d then Real.log l * (2 * C * D.R.f * D.R.m * L.sc.b) else 0) := by
      split_ifs; exact mul_nonneg (hlog0 l) hqd0; exact le_rfl
    have a4 : 0 ≤ (if l ≠ 2 ∧ l ≠ 3 ∧ (l : ℝ) ≤ lStar L then Real.log l * (bbB L C + lenB L C l) else 0) := by
      split_ifs; exact mul_nonneg (hlog0 l) (by linarith); exact le_rfl
    have a5 : 0 ≤ (if l ∈ tb.exc ∧ lStar L < l then Real.log l * (bbB L C + lenB L C l) else 0) := by
      split_ifs; exact mul_nonneg (hlog0 l) (by linarith); exact le_rfl
    unfold lamG
    by_cases hg : l ∈ gset D
    · rw [if_pos hg, if_pos hg]; linarith
    rw [if_neg hg]
    unfold lamB
    by_cases h23 : l ∈ D.host.small ∨ l = 3
    · rw [if_pos h23, if_pos h23]; linarith
    rw [if_neg h23]
    by_cases hqd : l = D.host.q ∨ l = D.host.d
    · rw [if_pos hqd, if_pos hqd]
      have : Real.log l * (2 * C * D.R.f * D.R.m * L.sc.b) = Real.log l * (2 * C * ↑D.R.f * ↑D.R.m * L.sc.b) := rfl
      linarith
    rw [if_neg hqd]
    by_cases he : lStar L < l ∧ l ∉ tb.exc
    · rw [if_pos he, mul_zero]; linarith
    rw [if_neg he]
    have h2 : l ≠ 2 := fun h => h23 (Or.inl (by rw [h]; exact two_mem_small D))
    have h3 : l ≠ 3 := fun h => h23 (Or.inr h)
    by_cases hs : (l : ℝ) ≤ lStar L
    · have e : (if l ≠ 2 ∧ l ≠ 3 ∧ (l : ℝ) ≤ lStar L then Real.log l * (bbB L C + lenB L C l) else 0) =
          Real.log l * (bbB L C + lenB L C l) := if_pos ⟨h2, h3, hs⟩
      linarith
    · push_neg at hs
      have hx : l ∈ tb.exc := by
        by_contra hx; exact he ⟨hs, hx⟩
      have e : (if l ∈ tb.exc ∧ lStar L < l then Real.log l * (bbB L C + lenB L C l) else 0) =
          Real.log l * (bbB L C + lenB L C l) := if_pos ⟨hx, hs⟩
      linarith
  have hsumle := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib] at hsumle
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter] at hsumle
  have s1 := sum_g L hC P hPar hL (S.filter (fun l => l ∈ gset D)) (fun l hl => (Finset.mem_filter.1 hl).2)
  have s2 := sum_23 L hC P hPar hL (S.filter (fun l => l ∈ D.host.small ∨ l = 3)) (fun l hl => (Finset.mem_filter.1 hl).2)
  have s3 := sum_qd L hC P hPar hL (S.filter (fun l => l = D.host.q ∨ l = D.host.d)) (fun l hl => (Finset.mem_filter.1 hl).2)
  have s4 := sum_small L hC P hPar hL (S.filter (fun l => l ≠ 2 ∧ l ≠ 3 ∧ (l : ℝ) ≤ lStar L)) (fun l hl => by
    obtain ⟨hlS, h⟩ := Finset.mem_filter.1 hl
    exact ⟨hS l hlS, h.1, h.2.1, h.2.2⟩)
  have s5 := sum_exc L hC P hPar hL tb hRe hExc (S.filter (fun l => l ∈ tb.exc ∧ lStar L < l)) (fun l hl => (Finset.mem_filter.1 hl).2)
  have gl := glob_le L hC P hPar hL
  have hbig := big_le_b L hC P hPar hL
  have hm := m_ge_one D
  have hf1 : (1 : ℝ) ≤ D.R.f := (m_ge_one D).trans (m_le_f D)
  have hL1 := L_ge_one L
  have hb := one_le_b L
  set X := (D.R.f : ℝ) * D.R.m * L.sc.b * large₂ L ^ 2 with hX
  have hbX : L.sc.b ≤ X := by
    have : (1 : ℝ) ≤ D.R.f * D.R.m * large₂ L ^ 2 := by
      have : (1 : ℝ) ≤ large₂ L ^ 2 := by nlinarith
      have : (1 : ℝ) ≤ D.R.f * D.R.m := by nlinarith
      nlinarith
    rw [hX]; nlinarith
  have hU0 : 0 ≤ Ub L C ^ 18 := by have := one_le_U L hC P hPar hL; positivity
  have e2 : 8 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 = 8 * C * X := by rw [hX]; ring
  have e3 : 4 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 = 4 * C * X := by rw [hX]; ring
  have e4 : 1000 * (C + 1) ^ 3 * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 = 1000 * (C + 1) ^ 3 * X := by rw [hX]; ring
  have hU : (20 + 2 + 1164000) * (C + 1) ^ 2 * Ub L C ^ 18 ≤ X := by
    have : (20 + 2 + 1164000) * (C + 1) ^ 2 * Ub L C ^ 18 ≤ 4 * 10 ^ 6 * (C + 1) ^ 2 * Ub L C ^ 18 := by
      have : 0 ≤ (C + 1) ^ 2 * Ub L C ^ 18 := by positivity
      nlinarith
    linarith
  have hX0 : 0 ≤ X := by positivity
  have hK : 1000 * (C + 1) ^ 3 * X + 8 * C * X + 4 * C * X + X ≤ 2000 * (C + 1) ^ 3 * X := by
    have h1 : 1000 * (C + 1) ^ 3 + 8 * C + 4 * C + 1 ≤ 2000 * (C + 1) ^ 3 := by
      have e : (C + 1) ^ 3 = C ^ 3 + 3 * C ^ 2 + 3 * C + 1 := by ring
      have : 0 ≤ C ^ 3 := by positivity
      have : 0 ≤ C ^ 2 := by positivity
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hX0
    linarith only [h2]
  have hsplit : (20 + 2 + 1164000) * (C + 1) ^ 2 * Ub L C ^ 18 = 20 * (C + 1) ^ 2 * Ub L C ^ 18 +
      2 * (C + 1) ^ 2 * Ub L C ^ 18 + 1164000 * (C + 1) ^ 2 * Ub L C ^ 18 := by ring
  linarith only [gl, hsumle, s1, s2, s3, s4, s5, e2, e3, e4, hU, hK, hsplit]

end Point

theorem Nc_nonneg : 0 ≤ L.Nc := by
  have hx0 : (0:ℝ) < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  show 0 ≤ (D.host.T2.card : ℝ) * D.R.k * Real.exp (L.sc.x ^ L.sc.eps) * L.sc.x ^ L.sc.eps /
    ((D.R.n : ℝ) * ((D.R.n : ℝ) * L.sc.x ^ (-L.sc.eps)))
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (Real.rpow_nonneg hx0.le _)
  · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (Real.rpow_nonneg hx0.le _))

theorem gset_ne_two (P : ParameterChoice' D L) : ∀ l ∈ gset D, l ≠ 2 := by
  obtain ⟨Y, hY1, -, -, hY4⟩ := P.g_Y
  have hk := k_ge_five D
  have hb := one_le_b L
  have h8 : (2 : ℝ) < ((D.R.k : ℝ) * L.sc.b) ^ 8 := by
    have : (5 : ℝ) ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have : (5 : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := by gcongr
    linarith
  intro l hl h2
  unfold gset at hl
  have hg : ∀ i, (2 : ℝ) < D.host.g i := fun i => by linarith [(hY4 i).1]
  rcases Finset.mem_insert.1 hl with h | h
  · have := hg 0; rw [← h, h2] at this; norm_num at this
  · have := hg 1; rw [← Finset.mem_singleton.1 h, h2] at this; norm_num at this

theorem export_bound_of_admissible (P : ParameterChoice' D L) {C : ℝ} (hL : Large L.sc.x L.sc.eps C) (hAdm : admitted L P C) :
    aux₃ L (2000 * (|C| + 1) ^ 3) := by
  classical
  intro hSha hsumm j hj
  obtain ⟨tb, hA⟩ := hAdm hSha
  have hC : 0 < C := lt_of_lt_of_le P.CLw_pos hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hPar : ParametersPolynomiallyBounded L C P := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have habs : |C| = C := abs_of_pos hC
  rw [habs]
  have h1 := etaSum_le L tb C P hA (gset_ne_two L P) hsumm hj
  set S := (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).image (fun w => D.what₂.places.resChar w) with hSdef
  have hSp : ∀ l ∈ S, l.Prime := by
    intro l hl
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hl
    exact D.what₂.places.resChar_prime w
  have h2 := point_bound L hC P hPar hL tb hA S hSp
  have hd0 : (0 : ℝ) ≤ L.dZ0 j := by positivity
  have hNc := Nc_nonneg L
  have hlx : 0 ≤ Real.log L.sc.x ^ 2 * L.Nc := by positivity
  have hK0 : 0 ≤ 2000 * (C + 1) ^ 3 := by positivity
  have h3 : 2000 * (C + 1) ^ 3 * (D.R.f * D.R.m * L.sc.b * large₂ L ^ 2) ≤
      2000 * (C + 1) ^ 3 * ((D.R.f : ℝ) * D.R.m * L.sc.b * (large₂ L) ^ 2 + (Real.log L.sc.x) ^ 2 * L.Nc) := by
    apply mul_le_mul_of_nonneg_left _ hK0; linarith
  calc etaSum L j ≤ (L.dZ0 j : ℝ) * (6 + UpperTheory.KStar.nuBudget D + Real.log (Formalism.MainNotions.N.hE D.host : ℝ) + Real.log (D.what₂.restRowsFiniteGroupCard : ℝ) +
        ∑ l ∈ S, Real.log l * lamG L tb C l) + (L.dZ0 j : ℝ) * ∑' l, vvTerm D l := h1
    _ ≤ (L.dZ0 j : ℝ) * (2000 * (C + 1) ^ 3 * ((D.R.f : ℝ) * D.R.m * L.sc.b * (large₂ L) ^ 2 +
        (Real.log L.sc.x) ^ 2 * L.Nc)) + (L.dZ0 j : ℝ) * ∑' l, vvTerm D l := by
        gcongr
        exact h2.trans h3
    _ = (L.dZ0 j : ℝ) * (2000 * (C + 1) ^ 3 * ((D.R.f : ℝ) * D.R.m * L.sc.b * (large₂ L) ^ 2 +
        (Real.log L.sc.x) ^ 2 * L.Nc) + ∑' l, vvTerm D l) := by ring

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions

private theorem eventually_log_mul_le_rpow_div_two (r K : ℝ) (hr : 0 < r) :
    ∀ᶠ x in Filter.atTop, Real.log x * K ≤ x ^ r / 2 := by
  have hc : (0:ℝ) < 1 / (2 * (|K| + 1)) := by positivity
  have h : ∀ᶠ x in Filter.atTop, ‖Real.log x‖ ≤ 1 / (2 * (|K| + 1)) * ‖x ^ r‖ :=
    (isLittleO_log_rpow_atTop hr).bound hc
  filter_upwards [h, Filter.eventually_ge_atTop (1:ℝ)] with x hx h1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg h1
  have hxr : 0 ≤ x ^ r := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hxr] at hx
  have hK1 : 1 / (2 * (|K| + 1)) * |K| ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith [abs_nonneg K]
  have h2 : Real.log x * K ≤ Real.log x * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) hlog
  have h3 : Real.log x * |K| ≤ 1 / (2 * (|K| + 1)) * x ^ r * |K| :=
    mul_le_mul_of_nonneg_right hx (abs_nonneg K)
  have h4 : 1 / (2 * (|K| + 1)) * x ^ r * |K| ≤ 1 / 2 * x ^ r := by
    calc 1 / (2 * (|K| + 1)) * x ^ r * |K| = (1 / (2 * (|K| + 1)) * |K|) * x ^ r := by ring
      _ ≤ 1 / 2 * x ^ r := mul_le_mul_of_nonneg_right hK1 hxr
  linarith

theorem large_eventually (eps C : ℝ) (heps : 0 < eps) : ∃ x0 : ℝ, ∀ x ≥ x0, Large x eps C := by
  have e2 : 0 < eps / 2 := by positivity
  have e3 : 0 < eps / 3 := by positivity
  have e23 : 0 < 2 * eps / 3 := by positivity
  have e12 : 0 < eps / 12 := by positivity
  have F3 := eventually_log_mul_le_rpow_div_two (eps / 3) 1 e3
  have F4 : ∀ᶠ x in Filter.atTop, 2 * Real.log 8 ≤ x ^ (eps / 3) :=
    (tendsto_rpow_atTop e3).eventually_ge_atTop _
  have F5 : ∀ᶠ x in Filter.atTop, (3:ℝ) ≤ x ^ eps := (tendsto_rpow_atTop heps).eventually_ge_atTop _
  have F6 : ∀ᶠ x in Filter.atTop, 48 * C ≤ x ^ ((1:ℝ) / 2) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  have F7 := eventually_log_mul_le_rpow_div_two (eps / 2) (|C + 3| + 1) e2
  have F8 : ∀ᶠ x in Filter.atTop, 2 * (|C + 3| + 1) ≤ x ^ (eps / 2) :=
    (tendsto_rpow_atTop e2).eventually_ge_atTop _
  have F9 := eventually_log_mul_le_rpow_div_two eps (C + 2) heps
  have WorkedExample : ∀ᶠ x in Filter.atTop, (2:ℝ) ≤ x ^ (2 * eps / 3) :=
    (tendsto_rpow_atTop e23).eventually_ge_atTop _
  have LargeParameterEstimates := eventually_log_mul_le_rpow_div_two (eps / 3) (20 * C + 40) e3
  have F12 : ∀ᶠ x in Filter.atTop, (40:ℝ) ≤ x ^ (eps / 12) :=
    (tendsto_rpow_atTop e12).eventually_ge_atTop _
  have hev : ∀ᶠ x in Filter.atTop, Large x eps C := by
    filter_upwards [Filter.eventually_ge_atTop (100:ℝ), Filter.eventually_ge_atTop (10 ^ 8 * (C + 1) ^ 3),
      F3, F4, F5, F6, F7, F8, F9, WorkedExample, LargeParameterEstimates, F12] with x f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
    have hx0 : 0 < x := by linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hX8 : 8 * x ≤ Real.exp (x ^ (eps / 3)) := by
      have h : Real.log (8 * x) ≤ x ^ (eps / 3) := by
        rw [Real.log_mul (by norm_num) hx0.ne']; linarith
      calc 8 * x = Real.exp (Real.log (8 * x)) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (x ^ (eps / 3)) := Real.exp_le_exp.mpr h
    have hb4 : 4 ≤ Real.exp (x ^ eps) := by linarith [Real.add_one_le_exp (x ^ eps)]
    have hs1 : x ^ eps = x ^ (eps / 3) * x ^ (2 * eps / 3) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hp3 : 0 ≤ x ^ (eps / 3) := Real.rpow_nonneg hx0.le _
    have hXb : x ^ (C + 2) * Real.exp (x ^ (eps / 3)) ≤ Real.exp (x ^ eps) := by
      rw [Real.rpow_def_of_pos hx0 (C + 2), ← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left f10 hp3]
    have hlg : (C + 3) ^ 2 * (1 + Real.log x) ^ 2 ≤ x ^ eps := by
      have hM1 : (|C + 3| + 1) * (1 + Real.log x) ≤ x ^ (eps / 2) := by linarith
      have hnn : 0 ≤ (|C + 3| + 1) * (1 + Real.log x) := mul_nonneg (by positivity) (by linarith)
      have hCM : (C + 3) ^ 2 ≤ (|C + 3| + 1) ^ 2 := by
        rw [← sq_abs (C + 3)]; nlinarith [abs_nonneg (C + 3)]
      calc (C + 3) ^ 2 * (1 + Real.log x) ^ 2 ≤ (|C + 3| + 1) ^ 2 * (1 + Real.log x) ^ 2 :=
            mul_le_mul_of_nonneg_right hCM (sq_nonneg _)
        _ = ((|C + 3| + 1) * (1 + Real.log x)) * ((|C + 3| + 1) * (1 + Real.log x)) := by ring
        _ ≤ x ^ (eps / 2) * x ^ (eps / 2) := mul_self_le_mul_self hnn hM1
        _ = x ^ eps := by rw [← Real.rpow_add hx0]; congr 1; ring
    have hex : x ^ (20 * C + 40) * Real.exp (20 * x ^ (eps / 4)) ≤ Real.exp (x ^ (eps / 3)) := by
      have hs2 : x ^ (eps / 3) = x ^ (eps / 4) * x ^ (eps / 12) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      have hp4 : 0 ≤ x ^ (eps / 4) := Real.rpow_nonneg hx0.le _
      rw [Real.rpow_def_of_pos hx0 (20 * C + 40), ← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left f12 hp4]
    exact ⟨f1, hX8, hb4, hXb, f6, hlg, hex, f2⟩
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp hev
  exact ⟨x0, fun x hx => hx0 x hx⟩

theorem stmtU_holds (eps : ℝ) : UniformExportStatement eps := by
  intro Ca
  refine ⟨2000 * (|Ca| + 1) ^ 3, ?_⟩
  intro Fm hA
  obtain ⟨x0, hx0⟩ := hA
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨xL, hxL⟩ := large_eventually eps Ca heps
  refine ⟨max x0 (max (Fm.x1 + 1) xL), ?_⟩
  intro x hx i
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨h0, h1, h2⟩ := hx
  have hx1 : Fm.x1 < x := by linarith
  have hLg : Large (Fm.L x i).sc.x (Fm.L x i).sc.eps Ca := by
    rw [Fm.L_x x i hx1, Fm.L_eps x i]; exact hxL x h2
  exact export_bound_of_admissible (Fm.L x i) (Fm.params x hx1 i) hLg (hx0 x h0 hx1 i)

theorem stmtF_holds {eps : ℝ} (Fm : FamP eps) : KudlaFamilyStatement Fm := stmtF_of_stmtU (stmtU_holds eps) Fm

end Formalism.MainNotions.TwistedPlaces

end
