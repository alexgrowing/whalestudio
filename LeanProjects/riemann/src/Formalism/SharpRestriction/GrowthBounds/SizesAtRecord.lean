import Formalism.SharpRestriction.GrowthBounds.Joints
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum
import Development.AutomorphicArithmetic.CyclotomicBounds.NotInert

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter
open Formalism.MainNotions Formalism.MainNotions.AuxBlock8

namespace Formalism.MainNotions.G.Joints

theorem DII_arith (x DII Np N1 r k lb n' c c0 b' : ℝ) (hx : 500 ≤ x) (hDII0 : 0 ≤ DII) (hNp0 : 0 ≤ Np) (hN10 : 0 ≤ N1)
    (hr0 : 0 ≤ r) (hk0 : 0 ≤ k) (hlb0 : 0 ≤ lb) (hn0 : 0 ≤ n') (hc0 : 0 ≤ c) (hc00 : 0 ≤ c0)
    (hDII : 480 * DII ≤ x) (hNp : Np ≤ 40 * x ^ 3) (hN1 : N1 ≤ x) (hr : r ≤ x) (hk : k ≤ x ^ 6) (hlb : lb ≤ 4 * x)
    (hn : n' ≤ x ^ 3) (hc : c ≤ b') (hc0' : c0 ≤ 5 * b') (hb : 1 ≤ b') :
    DII * Np * (N1 ^ 3 + r ^ 5 + k ^ 2) * lb + 2 * r * n' * c + r * Np * c0 + 1 ≤ x ^ 18 * b' := by

  have hx0 : (0:ℝ) ≤ x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hS : N1 ^ 3 + r ^ 5 + k ^ 2 ≤ 3 * x ^ 12 := by
    have a1 : N1 ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hN10 hN1 3
    have a2 : r ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ hr0 hr 5
    have a3 : k ^ 2 ≤ (x ^ 6) ^ 2 := pow_le_pow_left₀ hk0 hk 2
    have e3 : x ^ 3 ≤ x ^ 12 := pow_le_pow_right₀ hx1 (by norm_num)
    have e5 : x ^ 5 ≤ x ^ 12 := pow_le_pow_right₀ hx1 (by norm_num)
    have e6 : (x ^ 6) ^ 2 = x ^ 12 := by ring
    linarith
  have hS0 : 0 ≤ N1 ^ 3 + r ^ 5 + k ^ 2 :=
    add_nonneg (add_nonneg (pow_nonneg hN10 3) (pow_nonneg hr0 5)) (sq_nonneg k)
  have hA0 : 0 ≤ x / 480 * (40 * x ^ 3) :=
    mul_nonneg (div_nonneg hx0 (by norm_num)) (mul_nonneg (by norm_num) (pow_nonneg hx0 3))
  have h1 : DII * Np ≤ x / 480 * (40 * x ^ 3) := mul_le_mul (by linarith) hNp hNp0 (by linarith)
  have h2 : DII * Np * (N1 ^ 3 + r ^ 5 + k ^ 2) ≤ x / 480 * (40 * x ^ 3) * (3 * x ^ 12) :=
    mul_le_mul h1 hS hS0 hA0
  have h3 : DII * Np * (N1 ^ 3 + r ^ 5 + k ^ 2) * lb ≤ x / 480 * (40 * x ^ 3) * (3 * x ^ 12) * (4 * x) :=
    mul_le_mul h2 hlb hlb0 (mul_nonneg hA0 (mul_nonneg (by norm_num) (pow_nonneg hx0 12)))
  have h4 : 2 * r * n' * c ≤ 2 * x * x ^ 3 * b' :=
    mul_le_mul (mul_le_mul (by linarith) hn hn0 (by linarith)) hc hc0
      (mul_nonneg (by linarith) (pow_nonneg hx0 3))
  have h5 : r * Np * c0 ≤ x * (40 * x ^ 3) * (5 * b') :=
    mul_le_mul (mul_le_mul hr hNp hNp0 hx0) hc0' hc00 (mul_nonneg hx0 (mul_nonneg (by norm_num) (pow_nonneg hx0 3)))
  have hx17 : x ^ 4 ≤ x ^ 17 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx1
  have hB : 500 * x ^ 17 ≤ x ^ 18 := by
    have : x ^ 18 = x * x ^ 17 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hx (pow_nonneg hx0 17)
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hC : 500 * x ^ 17 * b' ≤ x ^ 18 * b' := mul_le_mul_of_nonneg_right hB hb0
  have h6 : x ^ 17 ≤ x ^ 17 * b' := le_mul_of_one_le_right (pow_nonneg hx0 17) hb
  have h7 : x ^ 4 * b' ≤ x ^ 17 * b' := mul_le_mul_of_nonneg_right hx17 hb0
  have h8 : 1 ≤ x ^ 17 * b' := one_le_mul_of_one_le_of_one_le (le_trans hx4 hx17) hb
  linarith [h3, h4, h5, h6, h7, h8, hC]

theorem SzII_arith (x sz k r N n' Q5 DIIc c c0 XA E2 b' R : ℝ) (hx : 500 ≤ x) (hsz0 : 0 ≤ sz) (hk0 : 0 ≤ k)
    (hr0 : 0 ≤ r) (hN0 : 0 ≤ N) (hn0 : 0 ≤ n') (hQ0 : 0 ≤ Q5) (hD0 : 0 ≤ DIIc) (hc0 : 0 ≤ c) (hc00 : 0 ≤ c0)
    (hsz : sz ≤ x) (hk : k ≤ x ^ 6) (hr : r ≤ x) (hN : N ≤ x ^ 3) (hn : n' ≤ x ^ 3) (hQ : Q5 ≤ E2)
    (hD : DIIc ≤ x ^ 18 * b') (hc : c ≤ b') (hc0' : c0 ≤ 5 * b') (hb : 1 ≤ b') (hXA : XA = x ^ 26)
    (hR : x ^ 69 * (E2 * b') ≤ R) :
    sz * k ^ 3 * r ^ 2 * N * Q5 * (8 * (DIIc + 1) + (r * N * c0 + 2 * r * n' * c)) * XA ≤ R := by

  have hx0 : (0:ℝ) ≤ x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hX0 : 0 ≤ x * (x ^ 6) ^ 3 := mul_nonneg hx0 (pow_nonneg (pow_nonneg hx0 6) 3)
  have hX1 : 0 ≤ x * (x ^ 6) ^ 3 * x ^ 2 := mul_nonneg hX0 (pow_nonneg hx0 2)
  have hP : sz * k ^ 3 * r ^ 2 * N ≤ x * (x ^ 6) ^ 3 * x ^ 2 * x ^ 3 :=
    mul_le_mul (mul_le_mul (mul_le_mul hsz (pow_le_pow_left₀ hk0 hk 3) (pow_nonneg hk0 3) hx0)
      (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg r) hX0) hN hN0 hX1
  have h_rNc0 : r * N * c0 ≤ x * x ^ 3 * (5 * b') :=
    mul_le_mul (mul_le_mul hr hN hN0 hx0) hc0' hc00 (mul_nonneg hx0 (pow_nonneg hx0 3))
  have h_rnc : 2 * r * n' * c ≤ 2 * x * x ^ 3 * b' :=
    mul_le_mul (mul_le_mul (by linarith) hn hn0 (by linarith)) hc hc0
      (mul_nonneg (by linarith) (pow_nonneg hx0 3))
  have hx14 : (15:ℝ) ≤ x ^ 14 := by
    have := pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 14)
    rw [pow_one] at this
    linarith
  have hx4b : 0 ≤ x ^ 4 * b' := mul_nonneg (pow_nonneg hx0 4) hb0
  have h15a : 15 * (x ^ 4 * b') ≤ x ^ 14 * (x ^ 4 * b') := mul_le_mul_of_nonneg_right hx14 hx4b
  have h15b : x ^ 14 * (x ^ 4 * b') = x ^ 18 * b' := by ring
  have h15c : 1 ≤ x ^ 4 * b' := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) hb
  have hI : 8 * (DIIc + 1) + (r * N * c0 + 2 * r * n' * c) ≤ 9 * x ^ 18 * b' := by
    linarith [hD, h_rNc0, h_rnc, h15a, h15b, h15c]
  have hI0 : 0 ≤ 8 * (DIIc + 1) + (r * N * c0 + 2 * r * n' * c) := by
    have : 0 ≤ r * N * c0 := mul_nonneg (mul_nonneg hr0 hN0) hc00
    have : 0 ≤ 2 * r * n' * c := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0) hn0) hc0
    linarith
  have hE0 : 0 ≤ E2 := le_trans hQ0 hQ
  have hQI : Q5 * (8 * (DIIc + 1) + (r * N * c0 + 2 * r * n' * c)) ≤ E2 * (9 * x ^ 18 * b') :=
    mul_le_mul hQ hI hI0 hE0
  have hPQI : sz * k ^ 3 * r ^ 2 * N * Q5 * (8 * (DIIc + 1) + (r * N * c0 + 2 * r * n' * c)) ≤
      x * (x ^ 6) ^ 3 * x ^ 2 * x ^ 3 * (E2 * (9 * x ^ 18 * b')) := by
    calc sz * k ^ 3 * r ^ 2 * N * Q5 * (8 * (DIIc + 1) + (r * N * c0 + 2 * r * n' * c))
        = (sz * k ^ 3 * r ^ 2 * N) * (Q5 * (8 * (DIIc + 1) + (r * N * c0 + 2 * r * n' * c))) := by ring
      _ ≤ _ := mul_le_mul hP hQI (mul_nonneg hQ0 hI0) (mul_nonneg hX1 (pow_nonneg hx0 3))
  have hEb : 0 ≤ E2 * b' := mul_nonneg hE0 hb0
  have h9 : 9 * x ^ 68 ≤ x ^ 69 := by
    have : x ^ 69 = x * x ^ 68 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hx0 68)
  rw [hXA]
  calc sz * k ^ 3 * r ^ 2 * N * Q5 * (8 * (DIIc + 1) + (r * N * c0 + 2 * r * n' * c)) * x ^ 26
      ≤ x * (x ^ 6) ^ 3 * x ^ 2 * x ^ 3 * (E2 * (9 * x ^ 18 * b')) * x ^ 26 :=
        mul_le_mul_of_nonneg_right hPQI (pow_nonneg hx0 26)
    _ = 9 * x ^ 68 * (E2 * b') := by ring
    _ ≤ x ^ 69 * (E2 * b') := mul_le_mul_of_nonneg_right h9 hEb
    _ ≤ R := hR

theorem localLength_le_ceil_log_mul {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) (hx : Real.exp 1 ≤ L.sc.x) (p : ℕ)
    (hp : p.Prime) : L1 D L.sc p ≤ ⌈256 * Real.log L.sc.x⌉₊ := by

  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, hK, -⟩ := hS'
  unfold Formalism.MainNotions.SizeK at hK
  unfold Formalism.MainNotions.szTh at hK
  unfold Formalism.MainNotions.G.L1
  apply Nat.ceil_le_ceil
  have hx0 : 0 < L.sc.x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlogx : 1 ≤ Real.log L.sc.x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hl2 : (0.69:ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogp0 : 0 < Real.log p := by linarith
  have heps := L.sc.eps_lt
  have hepos := L.sc.eps_pos
  have hA : Scale.A = 26 := rfl
  have hy : Real.log (((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4) ≤
      4 * ((9 / 2 + 10 * L.sc.eps + L.sc.eps / 100) + 26) * Real.log L.sc.x := by
    rcases Nat.eq_zero_or_pos D.R.k with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul, zero_pow (by norm_num), Real.log_zero]
      exact mul_nonneg (by linarith) (by linarith)
    · have hk0 : (0:ℝ) < D.R.k := by exact_mod_cast h0
      rw [Real.log_pow, Real.log_mul hk0.ne' (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0, hA]
      have hlk : Real.log D.R.k ≤ (9 / 2 + 10 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x := by
        have := Real.log_le_log hk0 hK.2
        rwa [Real.log_rpow hx0] at this
      push_cast
      nlinarith [hlk]
  rw [Real.logb, div_le_iff₀ hlogp0]
  have c1 : 4 * ((9 / 2 + 10 * L.sc.eps + L.sc.eps / 100) + 26) ≤ 123 := by linarith
  have c2 : 4 * ((9 / 2 + 10 * L.sc.eps + L.sc.eps / 100) + 26) * Real.log L.sc.x ≤ 123 * Real.log L.sc.x :=
    mul_le_mul_of_nonneg_right c1 (by linarith)
  have c3 : 256 * Real.log L.sc.x * 0.69 ≤ 256 * Real.log L.sc.x * Real.log p :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

theorem two_mul_localLength_le_maxLength {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) (hx : Real.exp 1 ≤ L.sc.x) (p : ℕ)
    (hp : p.Prime) (hc : IsResidueClassZero D p) : 2 * L1 D L.sc p ≤ L2 D L.sc := by

  unfold Formalism.MainNotions.G.L2
  gcongr
  apply le_csSup
  · refine ⟨⌈256 * Real.log L.sc.x⌉₊, ?_⟩
    rintro l ⟨q, hq, -, rfl⟩
    exact localLength_le_ceil_log_mul L hS hx q hq
  · exact ⟨p, hp, hc, rfl⟩

theorem thirteen_le {D : D7} (L : SizeData₂ D) (h13 : 13 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊) (p : ℕ) (hp : p.Prime)
    (hc0 : IsResidueClassZero D p) : 13 ≤ p := by

  by_contra hlt
  push_neg at hlt
  have hle : p ≤ D.host.splitBound := le_trans (le_of_lt hlt) (le_trans h13 L.split_tie)
  have hjac : jacobiSym (-(D.host.d : ℤ)) p = 1 := by
    rcases eq_or_ne p 2 with h2 | h2
    · subst h2
      have hd : D.host.d % 8 = 7 := by
        first
          | exact Formalism.HC.HostRaw.d_mod_eight
          | exact Formalism.HC.HostRaw.d_mod_eight _
          | exact Formalism.HC.HostRaw.d_mod_eight D.host.toHostAx
      have h2m : (-(D.host.d : ℤ)) % ((2:ℕ) : ℤ) = 1 := by push_cast; omega
      rw [jacobiSym.mod_left, h2m, jacobiSym.one_left]
    · exact D.host.split_small p hp h2 hle
  have hne : D.host.cls p ≠ PrimeClass.inertClass := by
    unfold Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass
    split_ifs <;> simp_all
  exact hne hc0

theorem Sc_le {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : L.Sc ≤ L.sc.b' / L.sc.x := by

  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, hK, -, -, -, -, -, hLa, -, -, -, -, -, -, -, hDel, -⟩ := hS'
  unfold Formalism.MainNotions.SizeK at hK
  unfold Formalism.MainNotions.SizeLa at hLa
  unfold Formalism.MainNotions.SizeDel at hDel
  unfold Formalism.MainNotions.szTh at hK hLa
  obtain ⟨-, -, -, -, -, hSc, -⟩ := hDel
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have heps : 0 < L.sc.eps := L.sc.eps_pos
  have hb : 0 < L.sc.b' := Formalism.BasicNotions.Scale.b'_pos (s := L.sc)
  have hk0 : (0:ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hK.1
  have key : L.LaG * L.sc.x ≤ D.R.k := by
    calc L.LaG * L.sc.x ≤ L.sc.x ^ (L.sc.eps + L.sc.eps / 100) * L.sc.x :=
          mul_le_mul_of_nonneg_right hLa.2 hx0.le
      _ = L.sc.x ^ (L.sc.eps + L.sc.eps / 100 + 1) := by
          rw [Real.rpow_add hx0 (L.sc.eps + L.sc.eps / 100) 1, Real.rpow_one]
      _ ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - L.sc.eps / 100) :=
          Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      _ ≤ D.R.k := hK.1
  have h1 : L.LaG * L.sc.b' / D.R.k = (L.LaG * L.sc.x) * (L.sc.b' / L.sc.x) / D.R.k := by
    field_simp
  have h2 : L.LaG * L.sc.b' / D.R.k ≤ L.sc.b' / L.sc.x := by
    rw [h1, div_le_iff₀ hk0, mul_comm (L.sc.b' / L.sc.x)]
    exact mul_le_mul_of_nonneg_right key (div_pos hb hx0).le
  have h3 : 0 < L.sc.b' / L.sc.x := div_pos hb hx0
  linarith

theorem Ib_le {D : D7} (L : SizeData₂ D) (K : Consts) (hK : K.Nonneg) (hrho : rho D K L.sc ≤ 1 / 7) :
    Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k ≤ L.sc.b' := by

  have hb : 0 < L.sc.b' := Formalism.BasicNotions.Scale.b'_pos (s := L.sc)
  have hK' := hK
  unfold Formalism.MainNotions.G.Consts.Nonneg at hK'
  obtain ⟨-, hrho0, -⟩ := hK'
  have hN : 0 ≤ Nstar D L.sc := by
    unfold Formalism.MainNotions.G.Nstar
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Formalism.MainNotions.J.delta1_pos L.sc).le
  have hxe : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hk : (0:ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hT : Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc / D.R.k ≤ 1 := by
    rcases le_or_gt 0 (La K L.sc) with hLa | hLa
    · have hS2 : 0 ≤ K.rho * (N1 L.sc : ℝ) * La K L.sc / D.R.k :=
        div_nonneg (mul_nonneg (mul_nonneg hrho0 (Nat.cast_nonneg _)) hLa) hk
      unfold Formalism.MainNotions.G.rho at hrho
      have h4 : 4 * Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc / D.R.k =
          4 * (Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc / D.R.k) := by ring
      linarith
    · have h0 : Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hN hxe) hLa.le
      have := div_nonpos_of_nonpos_of_nonneg h0 hk
      linarith
  calc Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k
      = (Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc / D.R.k) * L.sc.b' := by ring
    _ ≤ 1 * L.sc.b' := mul_le_mul_of_nonneg_right hT hb.le
    _ = L.sc.b' := one_mul _

theorem windows_at {D : D7} (L : SizeData₂ D) (K : Consts) (hK : K.Nonneg) (hS : Formalism.MainNotions.SizesAt L)
    (hLa : La K L.sc = L.LaG) (hrho : rho D K L.sc ≤ 1 / 7) (hx : 24 ≤ L.sc.x) (p : ℕ) (t0 : HH D) :
    (∀ s ∈ topsPos D p t0, wPos D p t0 (aL L) s ∈ winA D L.sc ∧ wPos D p t0 (bL L) s ∈ winB D K L.sc) ∧
    (∀ s ∈ topsPos D p t0, (L.sc.a - cG L) + (⌊cG L⌋₊ : ℝ) ≤ (wPos D p t0 (aL L) s : ℝ) ∧
      (wPos D p t0 (aL L) s : ℝ) ≤ 2 * (L.sc.a - cG L) - (⌊cG L⌋₊ : ℝ) ∧
      (wPos D p t0 (bL L) s : ℝ) + 2 * (⌊cG L⌋₊ : ℝ) ≤ c0num L) := by
  have hSc := Sc_le L hS
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hBot, -⟩ := hS'
  unfold Formalism.MainNotions.SizeBot at hBot
  have hIb := Ib_le L K hK hrho
  have hb0 : 0 < L.sc.b' := Formalism.BasicNotions.Scale.b'_pos (s := L.sc)
  have h2b := Formalism.MainNotions.G.TopChoiceBounds.two_b'_le_a₂ L.sc
  have hcG0 : 0 ≤ cG L := by
    unfold cG
    linarith [L.Sc_pos]
  have hcG : cG L ≤ L.sc.b' / 6 := by
    unfold cG
    have h24 : L.sc.b' / L.sc.x ≤ L.sc.b' / 24 :=
      div_le_div_of_nonneg_left hb0.le (by norm_num) hx
    linarith
  have hfl : (⌊cG L⌋₊ : ℝ) ≤ cG L := Nat.floor_le hcG0
  have hbT : ∀ t : D.host.TT, (L.bT t : ℝ) ≤
      L.sc.b' + Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k := by
    intro t
    rw [hLa]
    exact hBot t
  have hmem : ∀ s ∈ topsPos D p t0, t0 + (s : ℕ) • hP D p ∈ D.host.TT := fun s hs =>
    (Finset.mem_filter.mp hs).2
  have haw : ∀ s (hs : s ∈ topsPos D p t0), wPos D p t0 (aL L) s = L.aT ⟨_, hmem s hs⟩ := by
    intro s hs
    simp only [wPos, aL, dif_pos (hmem s hs)]
  have hbw : ∀ s (hs : s ∈ topsPos D p t0), wPos D p t0 (bL L) s = L.bT ⟨_, hmem s hs⟩ := by
    intro s hs
    simp only [wPos, bL, dif_pos (hmem s hs)]
  refine ⟨fun s hs => ⟨?_, ?_⟩, fun s hs => ⟨?_, ?_, ?_⟩⟩
  · rw [haw s hs]
    obtain ⟨h1, h2⟩ := L.aT_win ⟨_, hmem s hs⟩
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
  · rw [hbw s hs]
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (L.bT_ge _), Int.le_floor.mpr (hbT _)⟩
  · rw [haw s hs]
    have h1 := (L.aT_win ⟨_, hmem s hs⟩).1
    linarith
  · rw [haw s hs]
    have h1 := L.aT_le' ⟨_, hmem s hs⟩
    linarith
  · rw [hbw s hs]
    have h1 := hbT ⟨_, hmem s hs⟩
    unfold c0num
    linarith

def NumII (D : D7) (L : SizeData₂ D) (K : Consts) (p n' N : ℕ) : Prop :=
    N1 L.sc ^ 2 ≤ rG L.sc * N ∧
    (rG L.sc : ℝ) ≤ L.sc.x ^ Scale.A ∧
    (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A) ≤ (p : ℝ) ^ ((L1 D L.sc p : ℤ) - 1) ∧
    256 * (D.R.k : ℝ) ^ 2 * (N : ℝ) * (L.sc.x ^ Scale.A) ^ 2 ≤
      (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A) ∧
    N1 L.sc + 2 * rG L.sc + rG L.sc ≤ D.R.k ∧
    K.kII' * (N1 L.sc : ℝ) ^ 2 * Real.log L.sc.a ≤ D.R.k ∧
    K.szII * (D.R.k : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * (N : ℝ) * Qp L.sc p ^ 5 *
        ((8 * ((DIIf K L p n' : ℝ) + 1)) +
          ((rG L.sc : ℝ) * (N : ℝ) * c0num L +
            2 * (rG L.sc : ℝ) * ((n' : ℕ) : ℝ) * cG L)) *
        L.sc.x ^ Scale.A ≤ L.sc.a - cG L

set_option maxHeartbeats 2000000 in

theorem numII_ev (eps : ℝ) (K : Consts) (hK : K.Nonneg) (C31 : ℝ) (h31 : 0 < C31) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      ∀ p n' N : ℕ, p.Prime → (p : ℝ) < L.sc.p0 D.R.k → L.sc.x ^ (L.sc.eps / 4) ≤ (n' : ℝ) → n' ≤ D.R.n → N ≤ n' →
        (n' : ℝ) * L.sc.delta1 / (C31 * Real.log L.sc.x) ≤ (N : ℝ) → NumII D L K p n' N := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have F2 := Pf.ev_log (Pf.cNE eps) 1 one_pos
  have F6 := Pf.ev_log (Pf.cNE eps) (eps / 24) (by positivity)
  have F7 := Pf.ev_log C31 (eps / 24) (by positivity)
  have F8 := Pf.ev_pow (2 * K.kII') 3 (9 / 2) (by norm_num)
  have F9 := Pf.ev_log (38 * Pf.cGE eps) (eps / 96) (by positivity)
  have WorkedExample := Pf.ev_log 1 (eps / 96) (by positivity)
  have LargeParameterEstimates := Pf.ev_log 140 (eps / 3) (by positivity)
  have F12 := Pf.ev_pow 10 (eps / 8 + eps / 48) (eps / 3) (by linarith)
  filter_upwards [F2, F6, F7, F8, F9, WorkedExample, LargeParameterEstimates, F12, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop 500,
    eventually_ge_atTop ((Pf.rE eps : ℕ) : ℝ), eventually_ge_atTop K.szII, eventually_ge_atTop (480 * K.DII)] with
    x f2 f6 f7 f8 f9 f10 f11 f12 hxe hx500 hxr hxsz hxDII D L hx heps hS p n' N hp hp0 hn'lo hn'n hNn' hNlo
  clear F2 F6 F7 F8 F9 WorkedExample LargeParameterEstimates F12
  subst hx
  subst heps
  have hx0 := Pf.sc_x_pos L.sc
  have hx1 := L.sc.one_lt_alt
  have lx1 : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hk1 := Pf.one_le_k D
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := by linarith
  have hk6r := Pf.k_le_x_pow_six L hS
  have hk6 : (D.R.k : ℝ) ≤ L.sc.x ^ 6 := by
    rwa [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hk6r
  have hA26 : L.sc.x ^ Scale.A = L.sc.x ^ 26 := by
    rw [show Scale.A = ((26 : ℕ) : ℝ) by unfold Scale.A; norm_num, Real.rpow_natCast]
  have hA78 : L.sc.x ^ (3 * Scale.A) = L.sc.x ^ 78 := by
    rw [show 3 * Scale.A = ((78 : ℕ) : ℝ) by unfold Scale.A; norm_num, Real.rpow_natCast]
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hd0 := Pf.sc_delta1_pos L.sc
  have hScb := Sc_le L hS
  obtain ⟨hSN, -, hSK, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hSN
  unfold Formalism.MainNotions.SizeK Formalism.MainNotions.szTh at hSK
  have hklo : L.sc.x ^ (9 / 2 : ℝ) ≤ (D.R.k : ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) hSK.1
  have hk4 : L.sc.x ^ 4 ≤ (D.R.k : ℝ) := by
    refine le_trans ?_ hklo
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by
    have := le_trans hSN.2 (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : 2 + 8 * L.sc.eps + L.sc.eps / 100 ≤ (3 : ℝ)))
    rwa [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hn'3 : (n' : ℝ) ≤ L.sc.x ^ 3 := le_trans (by exact_mod_cast hn'n) hn3
  have hN3 : (N : ℝ) ≤ L.sc.x ^ 3 := le_trans (by exact_mod_cast hNn') hn'3
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hn'0 : (0 : ℝ) ≤ (n' : ℝ) := Nat.cast_nonneg _
  have hN1c := Pf.first_count_le_log L.sc hxe
  have hN1x : (N1 L.sc : ℝ) ≤ L.sc.x := by
    rw [Real.rpow_one] at f2
    linarith
  have hN10 : (0 : ℝ) ≤ (N1 L.sc : ℝ) := Nat.cast_nonneg _
  have hrx : (rG L.sc : ℝ) ≤ L.sc.x := hxr
  have hr0 : (0 : ℝ) ≤ (rG L.sc : ℝ) := Nat.cast_nonneg _
  have hxex : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : L.sc.eps ≤ (1 : ℝ))
    rwa [Real.rpow_one] at this
  have hloga : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlx : Real.log L.sc.x ≤ L.sc.x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hloga2 : Real.log L.sc.a ≤ 2 * L.sc.x := by rw [hloga]; linarith
  have hloga0 : 0 ≤ Real.log L.sc.a := Real.log_nonneg (Pf.sc_one_lt_a L.sc).le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (0 : ℝ) < p := by linarith
  have hp0' : (p : ℝ) < (D.R.k : ℝ) ^ 2 * L.sc.x ^ 26 := by
    have := hp0
    unfold Scale.p0 at this
    rwa [hA26] at this
  have hx126 : L.sc.x ≤ L.sc.x ^ 26 := by
    calc L.sc.x = L.sc.x ^ 1 := (pow_one _).symm
      _ ≤ L.sc.x ^ 26 := pow_le_pow_right₀ hx1.le (by norm_num)
  unfold NumII
  rw [hA26, hA78]
  refine ⟨?_, le_trans hrx hx126, ?_, ?_, ?_, ?_, ?_⟩
  ·
    set y := L.sc.x ^ (L.sc.eps / 24) with hy
    have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
    have hy3 : y ^ 3 = L.sc.x ^ (L.sc.eps / 4) * L.sc.delta1 := by
      unfold Scale.delta1
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      congr 1
      push_cast
      ring
    have hCl : 0 < C31 * Real.log L.sc.x := by positivity
    have h1 : (n' : ℝ) * L.sc.delta1 ≤ (N : ℝ) * (C31 * Real.log L.sc.x) := (div_le_iff₀ hCl).1 hNlo
    have h2 : y ^ 3 ≤ (N : ℝ) * y := by
      calc y ^ 3 = L.sc.x ^ (L.sc.eps / 4) * L.sc.delta1 := hy3
        _ ≤ (n' : ℝ) * L.sc.delta1 := by gcongr
        _ ≤ (N : ℝ) * (C31 * Real.log L.sc.x) := h1
        _ ≤ (N : ℝ) * y := by gcongr
    have h3 : y ^ 2 ≤ (N : ℝ) := by
      have : y ^ 2 * y ≤ (N : ℝ) * y := by
        calc y ^ 2 * y = y ^ 3 := by ring
          _ ≤ _ := h2
      exact le_of_mul_le_mul_right this hy0
    have h4 : (N1 L.sc : ℝ) ^ 2 ≤ (N : ℝ) := by
      calc (N1 L.sc : ℝ) ^ 2 ≤ y ^ 2 := by
            have : (N1 L.sc : ℝ) ≤ y := le_trans hN1c f6
            gcongr
        _ ≤ _ := h3
    have h5 : N1 L.sc ^ 2 ≤ N := by exact_mod_cast h4
    exact le_trans h5 (Nat.le_mul_of_pos_left _ (by unfold rG; omega))
  ·
    have hZ0 : 0 < ((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4 := by positivity
    have h1 : ((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4 ≤ (p : ℝ) ^ (L1 D L.sc p) := by
      have h := Nat.le_ceil (Real.logb p (((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4))
      have h' := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p) h
      rw [Real.rpow_logb hpp (by linarith) hZ0, Real.rpow_natCast] at h'
      exact h'
    rw [hA26] at h1
    rw [zpow_sub_one₀ hpp.ne', zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpp]
    calc (D.R.k : ℝ) ^ 2 * L.sc.x ^ 78 * p ≤ (D.R.k : ℝ) ^ 2 * L.sc.x ^ 78 * ((D.R.k : ℝ) ^ 2 * L.sc.x ^ 26) := by
          gcongr
      _ = ((D.R.k : ℝ) * L.sc.x ^ 26) ^ 4 := by ring
      _ ≤ _ := h1
  ·
    have h1 : 256 * (N : ℝ) ≤ L.sc.x ^ 26 := by
      calc 256 * (N : ℝ) ≤ L.sc.x * L.sc.x ^ 3 := by gcongr; linarith
        _ = L.sc.x ^ 4 := by ring
        _ ≤ L.sc.x ^ 26 := pow_le_pow_right₀ hx1.le (by norm_num)
    calc 256 * (D.R.k : ℝ) ^ 2 * (N : ℝ) * (L.sc.x ^ 26) ^ 2 = (D.R.k : ℝ) ^ 2 * (256 * (N : ℝ)) * L.sc.x ^ 52 := by ring
      _ ≤ (D.R.k : ℝ) ^ 2 * L.sc.x ^ 26 * L.sc.x ^ 52 := by gcongr
      _ = _ := by ring
  ·
    have h3 : L.sc.x ≤ L.sc.x ^ 3 := by
      calc L.sc.x = L.sc.x ^ 1 := (pow_one _).symm
        _ ≤ L.sc.x ^ 3 := pow_le_pow_right₀ hx1.le (by norm_num)
    have h4 : 4 * L.sc.x ≤ L.sc.x ^ 4 := by
      calc 4 * L.sc.x ≤ L.sc.x ^ 3 * L.sc.x := by gcongr; linarith
        _ = L.sc.x ^ 4 := by ring
    have h : (N1 L.sc : ℝ) + 2 * (rG L.sc : ℝ) + (rG L.sc : ℝ) ≤ (D.R.k : ℝ) := by
      calc (N1 L.sc : ℝ) + 2 * (rG L.sc : ℝ) + (rG L.sc : ℝ) ≤ L.sc.x + 2 * L.sc.x + L.sc.x := by gcongr
        _ = 4 * L.sc.x := by ring
        _ ≤ L.sc.x ^ 4 := h4
        _ ≤ _ := hk4
    exact_mod_cast h
  ·
    have hkII0 : 0 ≤ K.kII' := hK.2.2.2.2.2.2.1
    have h3' : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h3'] at f8
    calc K.kII' * (N1 L.sc : ℝ) ^ 2 * Real.log L.sc.a ≤ K.kII' * L.sc.x ^ 2 * (2 * L.sc.x) := by gcongr
      _ = 2 * K.kII' * L.sc.x ^ 3 := by ring
      _ ≤ _ := le_trans f8 hklo
  ·
    have hsz0 : 0 ≤ K.szII := hK.2.2.2.2.2.1
    have hDII0 : 0 ≤ K.DII := hK.2.2.2.2.1
    have hb0 := Pf.sc_b'_nonneg L.sc
    have hb1 : 1 ≤ L.sc.b' := by
      rw [Pf.b'_eq]
      have h1 : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x ^ L.sc.eps := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have h2 : 1 ≤ Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) := Real.one_le_exp (by linarith)
      nlinarith
    have hcG0 : 0 ≤ cG L := by unfold cG; have := L.Sc_pos; linarith
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb0 (by norm_num) (by linarith)
    have hcG : cG L ≤ L.sc.b' := by unfold cG; linarith
    have hc00 : 0 ≤ c0num L := by unfold c0num; linarith
    have hc0 : c0num L ≤ 5 * L.sc.b' := by
      unfold c0num
      linarith
    have hQ0 : 0 < Qp L.sc p := by unfold Qp; positivity
    have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlp : Real.log p ≤ 38 * Real.log L.sc.x := by
      have h1 : (p : ℝ) ≤ L.sc.x ^ 38 := by
        calc (p : ℝ) ≤ (D.R.k : ℝ) ^ 2 * L.sc.x ^ 26 := hp0'.le
          _ ≤ (L.sc.x ^ 6) ^ 2 * L.sc.x ^ 26 := by gcongr
          _ = L.sc.x ^ 38 := by ring
      have := Real.log_le_log hpp h1
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hcGE := Pf.cGE_nonneg L.sc.eps he0
    have hlQ : Real.log (Qp L.sc p) ≤ L.sc.x ^ (L.sc.eps / 8 + L.sc.eps / 48) := by
      unfold Qp
      rw [Real.log_pow]
      have hG := Pf.Gp_le L.sc hxe
      have hx8 : 0 ≤ L.sc.x ^ (L.sc.eps / 8) := Real.rpow_nonneg hx0.le _
      calc (Gp L.sc : ℝ) * Real.log p
          ≤ (Pf.cGE L.sc.eps * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) * (38 * Real.log L.sc.x) := by gcongr
        _ = (38 * Pf.cGE L.sc.eps * Real.log L.sc.x) * (1 * Real.log L.sc.x) * L.sc.x ^ (L.sc.eps / 8) := by ring
        _ ≤ L.sc.x ^ (L.sc.eps / 96) * L.sc.x ^ (L.sc.eps / 96) * L.sc.x ^ (L.sc.eps / 8) := by
            have q1 : 0 ≤ 1 * Real.log L.sc.x := by linarith
            gcongr
        _ = L.sc.x ^ (L.sc.eps / 8 + L.sc.eps / 48) := by
            rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
            congr 1
            ring
    have hQE : Qp L.sc p ≤ Real.exp (L.sc.x ^ (L.sc.eps / 8 + L.sc.eps / 48)) := by
      rw [← Real.exp_log hQ0]
      exact Real.exp_le_exp.2 hlQ
    have hlb0 : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg (by linarith) (Pf.sc_one_lt_a L.sc).le
    have hlb : Real.logb p L.sc.a ≤ 4 * L.sc.x := by
      unfold Real.logb
      have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hlp : (1 / 2 : ℝ) ≤ Real.log p := le_trans hl2 (Real.log_le_log (by norm_num) hp2)
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hNp0 : 0 ≤ NplusF L.sc n' := by unfold NplusF; positivity
    have hNp : NplusF L.sc n' ≤ 40 * L.sc.x ^ 3 := by
      unfold NplusF
      have := mul_le_mul hn'3 hd1 hd0.le (by positivity)
      nlinarith
    have hDIIf : ((DIIf K L p n' : ℕ) : ℝ) ≤ L.sc.x ^ 18 * L.sc.b' := by
      unfold DIIf
      have hW0 : 0 ≤ K.DII * NplusF L.sc n' * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) *
          Real.logb p L.sc.a + 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L + (rG L.sc : ℝ) * NplusF L.sc n' * c0num L := by
        positivity
      have h1 := Nat.ceil_lt_add_one hW0
      have h2 := DII_arith L.sc.x K.DII (NplusF L.sc n') (N1 L.sc : ℝ) (rG L.sc : ℝ) (D.R.k : ℝ)
        (Real.logb p L.sc.a) (n' : ℝ) (cG L) (c0num L) L.sc.b' hx500 hDII0 hNp0 hN10 hr0 hk0.le hlb0 hn'0 hcG0 hc00
        hxDII hNp hN1x hrx hk6 hlb hn'3 hcG hc0 hb1
      linarith
    apply SzII_arith L.sc.x K.szII _ _ _ _ _ _ _ _ _
      (Real.exp (L.sc.x ^ (L.sc.eps / 8 + L.sc.eps / 48)) ^ 5) L.sc.b' _ hx500 hsz0 hk0.le hr0 hN0 hn'0 (by positivity)
      (Nat.cast_nonneg _) hcG0 hc00 hxsz hk6 hrx hN3 hn'3 (by gcongr) hDIIf hcG hc0 hb1 rfl

    set E := Real.exp (L.sc.x ^ (L.sc.eps / 8 + L.sc.eps / 48)) ^ 5 with hE
    have hE1 : 1 ≤ E := one_le_pow₀ (Real.one_le_exp (Real.rpow_nonneg hx0.le _))
    have hX'0 : 0 < L.sc.X' := by unfold Scale.X'; exact Real.exp_pos _
    have hab : L.sc.a = L.sc.b' * L.sc.X' := by unfold Scale.b'; field_simp
    have hX : L.sc.x ^ 70 * E ≤ L.sc.X' := by
      have e1 : L.sc.x ^ 70 = Real.exp ((70 : ℕ) * Real.log L.sc.x) := by
        rw [Real.exp_nat_mul, Real.exp_log hx0]
      rw [hE, ← Real.exp_nat_mul, e1, ← Real.exp_add]
      unfold Scale.X'
      apply Real.exp_le_exp.2
      push_cast
      linarith
    have h69 : 1 ≤ L.sc.x ^ 69 := one_le_pow₀ hx1.le
    have h69E : 1 ≤ L.sc.x ^ 69 * E := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ L.sc.x ^ 69 * E := by gcongr
    have h70 : L.sc.x ^ 69 * E + 1 ≤ L.sc.X' := by
      have : 2 * (L.sc.x ^ 69 * E) ≤ L.sc.x ^ 70 * E := by
        calc 2 * (L.sc.x ^ 69 * E) ≤ L.sc.x * (L.sc.x ^ 69 * E) := by gcongr; linarith
          _ = L.sc.x ^ 70 * E := by ring
      linarith
    have := mul_le_mul_of_nonneg_right h70 hb0
    rw [hab]
    nlinarith

set_option maxHeartbeats 1000000 in

theorem hypIIAt_ev (eps ez : ℝ) (hez0 : 0 < ez) (K : Consts) (hK : K.Nonneg) (C31 : ℝ) (h31 : 0 < C31) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L), L.sc.x = x → L.sc.eps = eps → L.sc.ez = ez → Formalism.MainNotions.SizesAt L →
      La K L.sc = L.LaG → rho D K L.sc ≤ L.sc.x ^ (-2 : ℝ) → AuxBlock8.adm1 D L X C31 → HypIIAt D L X K := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have F1 := Pf.ev_pow 7 (-2) 0 (by norm_num)
  have F3 := Pf.ev_log 514 (eps / 8) (by positivity)
  have F4 := Pf.ev_log (3 * Pf.cGE eps) (eps / 8) (by positivity)
  have F5 := Pf.ev_pow 13 0 (ez / 5) (by positivity)
  filter_upwards [F1, F3, F4, F5, numII_ev eps K hK C31 h31, eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop 24] with x f1 f3 f4 f5 hnum hxe hx24 D L X hx heps hez hS hLa hrho h1
  clear F1 F3 F4 F5
  have hnum' := hnum D L hx heps hS
  clear hnum
  subst hx
  subst heps
  subst hez
  intro p hc hp0 t0 ht0
  have hx0 := Pf.sc_x_pos L.sc
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 / 7 := by
    rw [Real.rpow_zero] at f1; linarith
  have hL2u : L2 D L.sc < goodU L.sc.delta1 := Pf.second_level_lt_good_of_log L hS hxe f3
  have hGp : 3 * (Gp L.sc : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4) := by
    have hG := Pf.Gp_le L.sc hxe
    have hx8 : 0 ≤ L.sc.x ^ (L.sc.eps / 8) := Real.rpow_nonneg hx0.le _
    calc 3 * (Gp L.sc : ℝ) ≤ 3 * (Pf.cGE L.sc.eps * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) := by gcongr
      _ = (3 * Pf.cGE L.sc.eps * Real.log L.sc.x) * L.sc.x ^ (L.sc.eps / 8) := by ring
      _ ≤ L.sc.x ^ (L.sc.eps / 8) * L.sc.x ^ (L.sc.eps / 8) := by gcongr
      _ = L.sc.x ^ (L.sc.eps / 4) := by
          rw [← Real.rpow_add hx0]
          congr 1
          ring
  have hord3 : 3 * Gp L.sc ≤ addOrderOf (hP D p) := by
    have := le_trans hGp hc.2.2.2.1
    exact_mod_cast this
  obtain ⟨hr, hg⟩ := Pf.mem_goodReps ht0
  obtain ⟨hNlo, hN40⟩ := (h1 p hc.1 hc.2.2.1 hc.2.2.2.1 hL2u hord3 t0 hr hg).1
  rw [Pf.Nv_eq X p hc.2.2.1 t0 hr] at hNlo hN40
  have hNn' : (topsPos D p t0).card ≤ addOrderOf (hP D p) := by
    have := Finset.card_le_univ (topsPos D p t0)
    rwa [Fintype.card_fin] at this
  have h13 : 13 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊ := by
    apply Nat.le_floor
    rw [Real.rpow_zero] at f5
    push_cast
    linarith
  obtain ⟨hw1, hw2⟩ := windows_at L K hK hS hLa (le_trans hrho hx2) hx24 p t0
  have hr2 : 2 ≤ rG L.sc := by
    have : 0 < KG L.sc := by
      unfold KG
      apply Nat.ceil_pos.2
      unfold hG
      positivity
    unfold rG
    omega
  exact ⟨two_mul_localLength_le_maxLength L hS hxe p hc.1 hc.2.2.1, hL2u, hord3, hN40, hw1, hw2, thirteen_le L h13 p hc.1 hc.2.2.1, hr2,
    hnum' p _ _ hc.1 hp0 hc.2.2.2.1 (Pf.ord_le_n D _) hNn' hNlo⟩

theorem exists_place' (D : D7) : Nonempty D.what₂.places.Pl := by

  haveI := D.nfLL
  obtain ⟨P, hP0, hP⟩ := Ring.not_isField_iff_exists_prime.mp
    (NumberField.RingOfIntegers.not_isField (K := D.what₂.LL))
  exact ⟨D.plEq.symm ⟨P, hP, hP0⟩⟩

theorem hypIIAt_fam_of {eps : ℝ} (Fm : FamP eps) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm)
    (h1 : ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, AuxBlock8.adm1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) C) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, HypIIAt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK := by

  obtain ⟨C, hC, x0, hx0⟩ := h1
  obtain ⟨xc, hxc⟩ := hCN
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at this
  have hJ : 0 < Fm.J := by
    have := (Fm.L 0 i0).sc.one_le_J
    rw [Fm.L_J] at this
    linarith
  have hev := hypIIAt_ev eps (eps / Fm.J) (div_pos heps hJ) Fm.GK Fm.GK_nonneg C hC
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max x0 (max xc (max x2 (Fm.x1 + 1))), fun x hx i => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨hxa, hxb, hxd, hxe⟩ := hx
  have hx1 : Fm.x1 < x := by linarith
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hS := Fm.sizes x hx1 i
  have hLa : La Fm.GK (Fm.L x i).sc = (Fm.L x i).LaG := by
    obtain ⟨w⟩ := exists_place' (Fm.D x i)
    have hf := Fm.fills x hx1 i w
    unfold Formalism.MainNotions.G.ParametersFill at hf
    obtain ⟨-, -, -, -, -, -, h⟩ := hf
    exact h
  have hLaG : 0 < (Fm.L x i).LaG := by
    have hS' := hS
    unfold Formalism.MainNotions.SizesAt at hS'
    obtain ⟨-, -, -, -, -, -, -, -, hLa', -⟩ := hS'
    unfold Formalism.MainNotions.SizeLa at hLa'
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith [(Fm.L x i).sc.one_lt_alt]) _) hLa'.1
  have hK' := Fm.GK_nonneg
  unfold Formalism.MainNotions.G.Consts.Nonneg at hK'
  obtain ⟨-, hr0, -⟩ := hK'
  have hCb : CbLarge Fm.GK (Fm.L x i).sc := hxc x hxb i
  have hrho : rho (Fm.D x i) Fm.GK (Fm.L x i).sc ≤ (Fm.L x i).sc.x ^ (-2 : ℝ) := by
    rw [hLx]
    exact le_trans (Formalism.MainNotions.G.rho_le_rhoB _ _ _ hr0 (by rw [hLa]; exact hLaG.le) hCb) (Fm.rho_le x hx1 i)
  have hez : (Fm.L x i).sc.ez = eps / Fm.J := by
    unfold Formalism.BasicNotions.Scale.ez
    rw [Fm.L_eps, Fm.L_J]
  exact hx2 x hxd (Fm.D x i) (Fm.L x i) (Fm.Gx x i) hLx (Fm.L_eps x i) hez hS hLa hrho (hx0 x hxa i)

theorem hypIIAt_fam {eps : ℝ} (Fm : FamP eps) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, HypIIAt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK := by

  exact hypIIAt_fam_of Fm hCN (Formalism.MainNotions.G.TopChoiceBounds.family_uniform_constant_holds Fm)

end Formalism.MainNotions.G.Joints

end
