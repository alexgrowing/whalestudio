import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nodeGap_poly {x Y n f m k r t N M L S c₁ c₂ H : ℝ} (hx : 200 ≤ x) (hY : 1 ≤ Y)
    (hn0 : 0 ≤ n) (hf0 : 0 ≤ f) (hm1 : 1 ≤ m) (hk0 : 0 ≤ k) (hr0 : 0 ≤ r) (ht0 : 0 ≤ t) (hN0 : 0 ≤ N) (hM0 : 0 ≤ M)
    (hL0 : 0 ≤ L) (hS0 : 0 ≤ S)
    (hn : n ≤ x ^ 3) (hf : f ≤ x ^ 3) (hm : m ≤ x) (hk : k ≤ x ^ 5) (hr : r ≤ x ^ 5) (ht : t ≤ x ^ 401)
    (hN : N ≤ x ^ 402) (hM : M ≤ x ^ 402) (hL : L ≤ x) (hS : S ≤ x ^ 6 * Y) (h₁ : c₁ ≤ x) (h₂ : c₂ ≤ x)
    (hH : x ^ 1300 * Y ≤ H) :
    12 * ((n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L)) / m) + 2 * t + 8 ≤ H ∧ k * t * L ≤ H ∧
      c₁ * r ^ 19 * f ^ 5 * L ≤ H ∧ 4 * N ^ 3 + 2 * t + 6 ≤ H ∧ c₂ * k * m ^ ((9 : ℝ) / 2) ≤ H ∧
      2 * M ^ 3 + t + 3 ≤ H ∧ 120 * r * m ^ ((3 : ℝ) / 2) ≤ H ∧ N * m ^ 10 ≤ H ∧ 16 * m * N ≤ H := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have mono : ∀ a b : ℕ, a ≤ b → x ^ a ≤ x ^ b := fun a b h => pow_le_pow_right₀ hx1 h
  have hP : 0 ≤ x ^ 1299 := by positivity
  have hQ : x ^ 1299 ≤ x ^ 1299 * Y := le_mul_of_one_le_right hP hY
  have hH' : 200 * (x ^ 1299 * Y) ≤ H := by
    refine le_trans ?_ hH
    have : x ^ 1300 * Y = x * (x ^ 1299 * Y) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  have h1 : 1 ≤ x ^ 1299 := one_le_pow₀ hx1
  have ht' : t ≤ x ^ 1299 := ht.trans (mono _ _ (by norm_num))
  have hm92 : m ^ ((9 : ℝ) / 2) ≤ x ^ 5 := by
    calc m ^ ((9 : ℝ) / 2) ≤ m ^ ((5 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = m ^ 5 := Real.rpow_natCast _ _
      _ ≤ x ^ 5 := by gcongr
  have hm32 : m ^ ((3 : ℝ) / 2) ≤ x ^ 2 := by
    calc m ^ ((3 : ℝ) / 2) ≤ m ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = m ^ 2 := Real.rpow_natCast _ _
      _ ≤ x ^ 2 := by gcongr
  have hm0 : 0 ≤ m := by linarith
  have hN3 : N ^ 3 ≤ x ^ 1299 := by
    calc N ^ 3 ≤ (x ^ 402) ^ 3 := by gcongr
      _ = x ^ 1206 := by ring
      _ ≤ _ := mono _ _ (by norm_num)
  have hM3 : M ^ 3 ≤ x ^ 1299 := by
    calc M ^ 3 ≤ (x ^ 402) ^ 3 := by gcongr
      _ = x ^ 1206 := by ring
      _ ≤ _ := mono _ _ (by norm_num)
  refine ⟨?_, ?_, ?_, by linarith, ?_, by linarith, ?_, ?_, ?_⟩
  · have hA : n * t ^ 2 * (N + t) * L ^ 2 ≤ 2 * x ^ 1299 := by
      have ht2 : t ≤ x ^ 402 := ht.trans (mono _ _ (by norm_num))
      calc n * t ^ 2 * (N + t) * L ^ 2 ≤ x ^ 3 * (x ^ 401) ^ 2 * (x ^ 402 + x ^ 402) * x ^ 2 := by gcongr
        _ = 2 * x ^ 1209 := by ring
        _ ≤ _ := by have := mono 1209 1299 (by norm_num); linarith
    have hB : k * n ^ 2 * (S + t + L) ≤ 3 * (x ^ 1299 * Y) := by
      have hY0 : 0 ≤ Y := by linarith
      have hW : x ^ 401 ≤ x ^ 401 * Y := le_mul_of_one_le_right (by positivity) hY
      have hS' : S ≤ x ^ 401 * Y := hS.trans (mul_le_mul_of_nonneg_right (mono _ _ (by norm_num)) hY0)
      have ht2 : t ≤ x ^ 401 * Y := ht.trans hW
      have hL2 : L ≤ x ^ 401 * Y := by
        have := mono 1 401 (by norm_num)
        rw [pow_one] at this
        exact hL.trans (this.trans hW)
      calc k * n ^ 2 * (S + t + L) ≤ x ^ 5 * (x ^ 3) ^ 2 * (x ^ 401 * Y + x ^ 401 * Y + x ^ 401 * Y) := by gcongr
        _ = 3 * (x ^ 412 * Y) := by ring
        _ ≤ _ := by
          have := mul_le_mul_of_nonneg_right (mono 412 1299 (by norm_num)) hY0
          linarith
    have hD : (n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L)) / m ≤
        n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L) := div_le_self (by positivity) hm1
    linarith
  · have : k * t * L ≤ x ^ 1299 := by
      calc k * t * L ≤ x ^ 5 * x ^ 401 * x := by gcongr
        _ = x ^ 407 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : c₁ * r ^ 19 * f ^ 5 * L ≤ x ^ 1299 := by
      calc c₁ * r ^ 19 * f ^ 5 * L ≤ x * (x ^ 5) ^ 19 * (x ^ 3) ^ 5 * x := by gcongr
        _ = x ^ 112 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : c₂ * k * m ^ ((9 : ℝ) / 2) ≤ x ^ 1299 := by
      calc c₂ * k * m ^ ((9 : ℝ) / 2) ≤ x * x ^ 5 * x ^ 5 := by gcongr
        _ = x ^ 11 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : r * m ^ ((3 : ℝ) / 2) ≤ x ^ 1299 := by
      calc r * m ^ ((3 : ℝ) / 2) ≤ x ^ 5 * x ^ 2 := by gcongr
        _ = x ^ 7 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : N * m ^ 10 ≤ x ^ 1299 := by
      calc N * m ^ 10 ≤ x ^ 402 * x ^ 10 := by gcongr
        _ = x ^ 412 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : m * N ≤ x ^ 1299 := by
      calc m * N ≤ x * x ^ 402 := by gcongr
        _ = x ^ 403 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith

theorem szRow_nodeGap : SzRow (fun C D L => (12 * L.sc.b / lStar L + 2 * D.R.t + 8 ≤ h0 L ∧ (D.R.k : ℝ) * D.R.t * L.sc.L ≤ h0 L ∧ C.P.Ch0r * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ h0 L ∧ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ h0 L ∧ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ h0 L ∧ C.P.Ch0k * D.R.k * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) ≤ h0 L ∧ 2 * (Mrt D : ℝ) ^ 3 + D.R.t + 3 ≤ h0 L ∧ 120 * (D.R.r : ℝ) * (qSig D : ℝ) ^ ((3 : ℝ) / 2) ≤ h0 L ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ h0 L ∧ 16 * (qSig D : ℝ) * D.R.N D.R.m ≤ h0 L)) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD hcD => ⟨max (1300 + cD) (406 * |C.P.CCount|), fun ch hch =>
    ⟨max (max x1 200) (max C.P.Ch0r C.P.Ch0k), fun D L hε hx hV => ?_⟩⟩⟩
  simp only [max_le_iff, ge_iff_le] at hx hch
  obtain ⟨⟨hxa, hxb⟩, hxc, hxd⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ := hx1 L.sc D.R hε hxa hV.ranks
  have hxone : 1 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a := fun a => Real.rpow_natCast _ _
  have hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by rw [← cast]; exact_mod_cast hf
  have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by rw [← cast]; exact_mod_cast hr
  have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by rw [← cast]; exact_mod_cast ht
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402 := by rw [← cast]; exact_mod_cast hN
  have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
  have hnf : (D.R.n : ℝ) ≤ D.R.f := by
    have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have hm2 := D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hMN : (Mrt D : ℝ) ≤ D.R.N D.R.m := by
    have : Mrt D ≤ D.R.N D.R.m := by
      unfold Mrt Ranks.N Ranks.r
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact_mod_cast this
  have hY : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hxone hcD
  have hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; ring
  have hS0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  have hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD := by
    rw [hSc]
    calc (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) ≤ L.sc.x ^ 5 * (4 * (2 * L.sc.x ^ cD)) := by gcongr
      _ = L.sc.x ^ 5 * 8 * L.sc.x ^ cD := by ring
      _ ≤ L.sc.x ^ 5 * L.sc.x * L.sc.x ^ cD := by gcongr; linarith
      _ = _ := by ring
  have hh0 : L.sc.x ^ ch ≤ h0 L := by
    have e : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0; rw [hV.eta_eq]; field_simp
    have := Nat.le_ceil (L.sc.x ^ ch)
    have h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ) := Nat.cast_nonneg _
    rw [e]; unfold h0v; push_cast; linarith
  have hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ h0 L := by
    refine le_trans ?_ hh0
    rw [← cast, ← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch.1)
  obtain ⟨a1, a2, a3, a5, a6, a7, a8, a9, a10⟩ := nodeGap_poly (c₁ := C.P.Ch0r) (c₂ := C.P.Ch0k) hxb hY
    (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r)
    (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m)) (Nat.cast_nonneg (Mrt D)) (by linarith : 0 ≤ L.sc.L) hS0
    (hnf.trans hf') hf' hm hk' hr' ht' hN' (hMN.trans hN') hL hS hxc hxd hH
  refine ⟨?_, a2, a3, ?_, a5, a6, a7, a8, a9, a10⟩
  · have hb : 0 < L.sc.b := by unfold Scale.b; positivity
    refine le_trans (le_of_eq ?_) a1
    unfold lStar
    rw [div_div_eq_mul_div]
    field_simp
  · have hf1 : (1 : ℝ) ≤ D.R.f := by
      have : 1 ≤ D.R.f := le_trans (by omega) D.R.m_le_f
      exact_mod_cast this
    have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by
      have := D.R.m_add_three_le_k
      have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; omega
      exact_mod_cast this
    have hB1 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN1 hf1) hL1
    have hB : (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L ≤ L.sc.x ^ (406 : ℝ) := by
      calc (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L ≤ L.sc.x ^ 402 * L.sc.x ^ 3 * L.sc.x := by gcongr
        _ = L.sc.x ^ 406 := by ring
        _ = _ := by rw [← cast]; norm_num
    calc _ ≤ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ |C.P.CCount| :=
          Real.rpow_le_rpow_of_exponent_le hB1 (le_abs_self _)
      _ ≤ (L.sc.x ^ (406 : ℝ)) ^ |C.P.CCount| := Real.rpow_le_rpow (by linarith) hB (abs_nonneg _)
      _ = L.sc.x ^ (406 * |C.P.CCount|) := (Real.rpow_mul hxpos.le _ _).symm
      _ ≤ L.sc.x ^ ch := Real.rpow_le_rpow_of_exponent_le hxone hch.2
      _ ≤ _ := hh0

end GlobalTheory.EX
