import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

namespace GlobalTheory.BigTop.Fun.PolBound

theorem log_le_posLog' (y : ℝ) : Real.log y ≤ Real.posLog y := by
  unfold Real.posLog; exact le_max_right _ _

theorem posLog_le_of_log_le {y B : ℝ} (hy : Real.log y ≤ B) (hB : 0 ≤ B) : Real.posLog y ≤ B := by
  unfold Real.posLog; exact max_le hB hy

theorem pol_core {C Q f m k t lb Lb : ℝ} (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hf0 : 0 ≤ f) (hf : f ≤ Q) (hm0 : 0 ≤ m)
    (hm : m ≤ Q) (hk0 : 0 ≤ k) (hk : k ≤ Q) (ht0 : 0 ≤ t) (ht : t ≤ Q) (hlb0 : 0 ≤ lb) (hlb : lb ≤ Q)
    (hLb : Lb ≤ 20 * Q) :
    100000 * C ^ 3 * f * m ^ 2 * (k + m * (t + (k + m + 5) + 1)) ^ 2 *
      ((k + m - 1) * (k + m * (t + (k + m + 5) + 1)) * lb + C * f ^ 2 * (k + m) ^ 6 * Lb) ≤
      13000000000 * C ^ 4 * Q ^ 16 := by
  set N := k + m * (t + (k + m + 5) + 1) with hNdef
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hN0 : 0 ≤ N := by positivity
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hN : N ≤ 10 * Q ^ 2 := by
    have h1 : t + (k + m + 5) + 1 ≤ 9 * Q := by linarith
    have h2 : m * (t + (k + m + 5) + 1) ≤ Q * (9 * Q) := mul_le_mul hm h1 (by positivity) hQ0
    nlinarith
  have hr : k + m - 1 ≤ 2 * Q := by linarith
  have hnr0 : 0 ≤ k + m := by linarith
  have hnr : k + m ≤ 2 * Q := by linarith
  have i1 : (k + m - 1) * N * lb ≤ (2 * Q) * (10 * Q ^ 2) * Q := by
    have a : (k + m - 1) * (N * lb) ≤ (2 * Q) * (N * lb) := mul_le_mul_of_nonneg_right hr (by positivity)
    have b : N * lb ≤ (10 * Q ^ 2) * Q := mul_le_mul hN hlb hlb0 (by positivity)
    have c : (2 * Q) * (N * lb) ≤ (2 * Q) * ((10 * Q ^ 2) * Q) := mul_le_mul_of_nonneg_left b (by positivity)
    calc (k + m - 1) * N * lb = (k + m - 1) * (N * lb) := by ring
      _ ≤ _ := a.trans c
      _ = _ := by ring
  have i2 : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) := by
    have a : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * f ^ 2 * (k + m) ^ 6 * (20 * Q) :=
      mul_le_mul_of_nonneg_left hLb (by positivity)
    have b : C * f ^ 2 * (k + m) ^ 6 ≤ C * Q ^ 2 * (2 * Q) ^ 6 := by gcongr
    exact a.trans (mul_le_mul_of_nonneg_right b (by positivity))
  have hQ4 : Q ^ 4 ≤ Q ^ 9 := pow_le_pow_right₀ hQ (by norm_num)
  have hinner : (k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb ≤ 1300 * C * Q ^ 9 := by
    have e1 : (2 * Q) * (10 * Q ^ 2) * Q = 20 * Q ^ 4 := by ring
    have e2 : C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) = 1280 * C * Q ^ 9 := by ring
    have e3 : 20 * Q ^ 4 ≤ 20 * C * Q ^ 9 := by
      have : Q ^ 4 ≤ C * Q ^ 9 := hQ4.trans (le_mul_of_one_le_left (by positivity) hC)
      linarith
    linarith
  have hpre0 : 0 ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 := by positivity
  have hpre : 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 := by gcongr
  calc 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * ((k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb)
      ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * (1300 * C * Q ^ 9) := mul_le_mul_of_nonneg_left hinner hpre0
    _ ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 * (1300 * C * Q ^ 9) :=
        mul_le_mul_of_nonneg_right hpre (by positivity)
    _ = 13000000000 * C ^ 4 * Q ^ 16 := by ring

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun.PolBound

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem rpow_mono {x a b : ℝ} (hx : 1 ≤ x) (h : a ≤ b) : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx h

theorem factors_le {D : D7} (L : SizeData₂ D) (hS : SizesAt L) (T : ℕ) (hT : L.Ct + 1 ≤ T) :
    (D.R.f : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.m : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.k : ℝ) ≤ L.sc.x ^ (T + 9) ∧
      (D.R.t : ℝ) ≤ L.sc.x ^ (T + 9) ∧ Real.log L.sc.b ≤ L.sc.x ^ (T + 9) ∧ 0 ≤ Real.log L.sc.b ∧
      Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ 20 * L.sc.x ^ (T + 9) := by
  obtain ⟨hN, hM, hK, hKR, hTt, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, hPde, -⟩ := hS
  set x := L.sc.x with hxdef
  have hx1 : 1 ≤ x := L.sc.one_lt_alt.le
  have hx0 : 0 ≤ x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have hth : szTh L = L.sc.eps / 100 := rfl
  have hpow : ∀ j : ℕ, j ≤ T + 9 → x ^ j ≤ x ^ (T + 9) := fun j hj => pow_le_pow_right₀ hx1 hj
  have hrp : ∀ (a : ℝ) (j : ℕ), a ≤ j → x ^ a ≤ x ^ j := fun a j h => by
    rw [← Real.rpow_natCast]; exact rpow_mono hx1 h

  have hLd : L.sc.L = x ^ L.sc.eps := by rw [hxdef]; rfl
  have hlb : Real.log L.sc.b = x ^ L.sc.eps := by
    show Real.log (Real.exp L.sc.L) = _
    rw [Real.log_exp]; exact hLd
  have hLx : x ^ L.sc.eps ≤ x := by
    have := hrp L.sc.eps 1 (by norm_num; linarith); simpa using this

  have hm : (D.R.m : ℝ) ≤ x := by
    have hd1 : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0 _
    have h1 : Real.sqrt (x * L.sc.delta1) ≤ x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : x ^ szTh L * Real.sqrt (x * L.sc.delta1) ≤ x ^ szTh L * x ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx0 _)
    rw [← Real.rpow_add (by linarith)] at h2
    have h3 : x ^ (szTh L + 1 / 2) ≤ x ^ (1 : ℕ) := hrp _ 1 (by rw [hth]; push_cast; linarith)
    linarith [hM.2, pow_one x]
  have hk : (D.R.k : ℝ) ≤ x ^ 5 := hK.2.trans (hrp _ 5 (by rw [hth]; push_cast; linarith))
  have hn : (D.R.n : ℝ) ≤ x ^ 3 := hN.2.trans (hrp _ 3 (by rw [hth]; push_cast; linarith))
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf : (D.R.f : ℝ) ≤ x ^ 5 := by
    have h := hKR.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h2 : (D.R.m : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hm0 hm 2
    have h3 : (D.R.m : ℝ) ^ 2 * D.R.n ≤ x ^ 2 * x ^ 3 := mul_le_mul h2 hn (Nat.cast_nonneg _) (by positivity)
    calc (D.R.f : ℝ) ≤ _ := h
      _ ≤ _ := h3
      _ = x ^ 5 := by ring
  have ht : (D.R.t : ℝ) ≤ x ^ T := by
    refine hTt.2.trans (hrp _ T ?_)
    have : L.Ct + szTh L ≤ L.Ct + 1 := by rw [hth]; linarith
    linarith
  have hQ5 : x ^ 5 ≤ x ^ (T + 9) := hpow 5 (by omega)
  have hQ8 : x ^ 8 ≤ x ^ (T + 9) := hpow 8 (by omega)
  have hQ1 : x ≤ x ^ (T + 9) := by simpa using hpow 1 (by omega)
  refine ⟨hf.trans hQ5, hm.trans hQ1, hk.trans hQ5, ht.trans (hpow T (by omega)), by rw [hlb]; linarith,
    by rw [hlb]; positivity, ?_⟩

  have hb : Real.posLog L.sc.b ≤ x := posLog_le_of_log_le (by rw [hlb]; exact hLx) hx0
  have hnr : Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) ≤ 2 * x ^ 5 := by
    refine posLog_le_of_log_le ((Real.log_le_self (Nat.cast_nonneg _)).trans ?_) (by positivity)
    push_cast
    have : (D.R.m : ℝ) ≤ x ^ 5 := hm.trans (by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 5))
    linarith
  have hg : ∀ i : Fin 2, Real.posLog (D.host.g i : ℝ) ≤ x := fun i => by
    refine posLog_le_of_log_le ((hG i i).2.2.trans ?_) hx0
    rw [hLd, ← Real.rpow_add (by linarith)]
    have := hrp (szTh L + L.sc.eps) 1 (by rw [hth]; push_cast; linarith)
    simpa using this
  have hp1 : Real.posLog (D.host.pde : ℝ) ≤ x := posLog_le_of_log_le (hPde.1.trans (hLd ▸ hLx)) hx0
  have hp2 : Real.posLog (D.host.pde' : ℝ) ≤ x := posLog_le_of_log_le (hPde.2.trans (hLd ▸ hLx)) hx0
  have hdE : Real.posLog |((discr D.host.E : ℤ) : ℝ)| ≤ 6 * x ^ 8 := by
    refine posLog_le_of_log_le ?_ (by positivity)
    have e := logdE_eq_rd D
    unfold logdE at e
    rw [e]
    have hlr : Real.log D.host.rdE ≤ 2 * x ^ 3 + x := by
      have h1 := UpperTheory.Ram.Rd.log_rdE_le D.host
      have h2 : Real.log (D.R.n : ℝ) ≤ x ^ 3 := (Real.log_le_self (Nat.cast_nonneg _)).trans hn
      have hq : Real.log D.host.q ≤ x := hQD.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      have hd : Real.log D.host.d ≤ x := hQD.2.2.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      linarith
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    calc 2 * (D.R.f : ℝ) * Real.log D.host.rdE ≤ 2 * (D.R.f : ℝ) * (2 * x ^ 3 + x) :=
          mul_le_mul_of_nonneg_left hlr (by positivity)
      _ ≤ 2 * x ^ 5 * (2 * x ^ 3 + x) := by gcongr
      _ ≤ 6 * x ^ 8 := by
          have : x ^ 6 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
          nlinarith
  have hprod : Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ Real.posLog L.sc.b + Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) +
      Real.posLog (D.host.g 0 : ℝ) + Real.posLog (D.host.g 1 : ℝ) + Real.posLog (D.host.pde : ℝ) +
      Real.posLog (D.host.pde' : ℝ) + Real.posLog |((discr D.host.E : ℤ) : ℝ)| := by
    refine (log_le_posLog' _).trans ?_
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    exact Real.posLog_mul
  have h8 : x ^ 5 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
  have h18 : x ≤ x ^ 8 := by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 8)
  have := hg 0
  have := hg 1
  refine hprod.trans ?_
  linarith

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound

theorem desPol : DesPol := by
  refine ⟨0, fun CF _ => ?_⟩
  refine ⟨1 / 52, by norm_num, fun eps _ _ =>
    ⟨⟨0, fun _ => 0, fun l => 16 * ((⌈|l.getD 0 0|⌉₊ : ℝ) + 1 + 9) + 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  intro _
  have hCH : 16 * ((⌈|Fm.Ct|⌉₊ : ℝ) + 1 + 9) + 1 ≤ CH := hL.2.2.1 CH (by simp [FamP.cMid])
  refine ⟨1, fun C hC => ?_⟩
  refine ⟨max (13000000000 * C ^ 4) 1, fun x hx hxle i p _ d _ => ?_⟩
  set T : ℕ := ⌈|Fm.Ct|⌉₊ + 1 with hTdef
  have hT : (Fm.L x i).Ct + 1 ≤ T := by
    rw [Fm.Ct_eq, hTdef]; push_cast; linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := factors_le (Fm.L x i) (Fm.sizes x hx i) T hT
  set X := (Fm.L x i).sc.x with hXdef
  have hX1 : 1 ≤ X := (Fm.L x i).sc.one_lt_alt.le
  have hXA : 13000000000 * C ^ 4 ≤ X := by
    rw [hXdef, Fm.L_x x i hx]; exact (le_max_left _ _).trans hxle
  set D := Fm.D x i
  have eN : ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) =
      (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) := by push_cast; ring
  have enr : ((D.R.k + D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m := by push_cast; ring
  have e : d.O.pol C p.Z.b = 100000 * C ^ 3 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 *
      ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) ^ 2 *
      (((D.R.k : ℝ) + D.R.m - 1) * ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) *
        Real.log (Fm.L x i).sc.b + C * (D.R.f : ℝ) ^ 2 * ((D.R.k + D.R.m : ℕ) : ℝ) ^ 6 *
        Real.log ((Fm.L x i).sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) *
          (D.host.pde : ℝ) * (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|)) := rfl
  show d.O.pol C p.Z.b ≤ X ^ CH
  rw [e, eN, enr]
  rw [enr] at h7
  have key := pol_core hC (one_le_pow₀ hX1) (Nat.cast_nonneg _) h1 (Nat.cast_nonneg _) h2 (Nat.cast_nonneg _) h3
    (Nat.cast_nonneg _) h4 h6 h5 h7
  refine key.trans ?_
  have hp : (X ^ (T + 9)) ^ 16 = X ^ (16 * (T + 9)) := by rw [← pow_mul, mul_comm]
  have hC4 : 0 ≤ 13000000000 * C ^ 4 := by positivity
  calc 13000000000 * C ^ 4 * (X ^ (T + 9)) ^ 16 ≤ X * X ^ (16 * (T + 9)) := by
        rw [hp]; exact mul_le_mul_of_nonneg_right hXA (by positivity)
    _ = X ^ ((16 * (T + 9) + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_succ, mul_comm]
    _ ≤ X ^ CH := by
        refine rpow_mono hX1 ?_
        rw [hTdef] at *
        push_cast
        linarith

end GlobalTheory.BigTop.Fun
