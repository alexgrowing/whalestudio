import Mathlib
import Formalism.PolynomialDimension.DigitClassSize

noncomputable section

open scoped BigOperators
open Finset Filter Topology

namespace Formalism.CountingSumsFrames

theorem dimPol_pos_real (k' A : ℕ) : (0 : ℝ) < dimPol k' A := by
  unfold dimPol
  exact_mod_cast Nat.choose_pos (by omega)

theorem dimPol_succ_mul_real (k' A : ℕ) :
    (dimPol k' (A + 1) : ℝ) * ((A : ℝ) + 1) = dimPol k' A * ((A : ℝ) + 1 + k') := by
  have h := Nat.choose_mul_succ_eq (A + k') k'
  rw [show A + k' + 1 - k' = A + 1 by omega] at h
  have h3 : dimPol k' (A + 1) * (A + 1) = dimPol k' A * (A + 1 + k') := by
    unfold dimPol
    rw [show A + 1 + k' = A + k' + 1 by omega]
    exact h.symm
  exact_mod_cast h3

theorem dimPol_succ_eq_real (k' A : ℕ) :
    (dimPol k' (A + 1) : ℝ) = dimPol k' A * ((A : ℝ) + 1 + k') / ((A : ℝ) + 1) := by
  rw [eq_div_iff (by positivity)]
  exact dimPol_succ_mul_real k' A

theorem binomial_ratio_bound : BinomRatio := by
  intro k' al j hal
  have hal' : (0 : ℝ) < al := by exact_mod_cast hal
  induction j with
  | zero => simp [div_self (dimPol_pos_real k' al).ne']
  | succ j ih =>
    have p0 := dimPol_pos_real k' (al + j)
    have pa := dimPol_pos_real k' al
    have hrec := dimPol_succ_eq_real k' (al + j)
    rw [show al + (j + 1) = al + j + 1 by omega, hrec]
    push_cast at ih ⊢
    set r : ℝ := (dimPol k' al : ℝ) / dimPol k' (al + j) with hr
    have hr0 : 0 ≤ r := by positivity
    have hkey : (dimPol k' al : ℝ) / (dimPol k' (al + j) * ((al : ℝ) + j + 1 + k') / ((al : ℝ) + j + 1))
        = r * (((al : ℝ) + j + 1) / ((al : ℝ) + j + 1 + k')) := by
      rw [hr]; field_simp
    rw [hkey]
    set t : ℝ := ((al : ℝ) + j + 1) / ((al : ℝ) + j + 1 + k') with ht
    have hk0 : (0 : ℝ) ≤ k' := by positivity
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; linarith
    have h1t : 1 - t ≤ (k' : ℝ) / al := by
      have : 1 - t = (k' : ℝ) / ((al : ℝ) + j + 1 + k') := by rw [ht]; field_simp; ring
      rw [this]
      exact div_le_div_of_nonneg_left hk0 hal' (by linarith)
    have hexp : 1 - (k' : ℝ) * (j + 1) / al = (1 - (k' : ℝ) * j / al) - k' / al := by ring
    rw [hexp]
    by_cases ha : 1 - (k' : ℝ) * j / al ≤ 0
    · have : (0 : ℝ) ≤ k' / al := by positivity
      nlinarith [mul_nonneg hr0 ht0]
    · rw [not_le] at ha
      set a := 1 - (k' : ℝ) * j / al
      have ha1 : a ≤ 1 := by
        have : (0 : ℝ) ≤ k' * j / al := by positivity
        linarith
      have h2 : a * t ≤ r * t := mul_le_mul_of_nonneg_right ih ht0
      have h3 : a * (1 - t) ≤ 1 - t := by nlinarith
      nlinarith

theorem binomSeries_gen (k' B : ℕ) (hk : 2 ≤ k') :
    HasSum (fun j : ℕ => (dimPol k' B : ℝ) / dimPol k' (B + j)) (((B : ℝ) + k') / ((k' : ℝ) - 1)) := by
  have hk2 : (2 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have pB := dimPol_pos_real k' B
  set g : ℕ → ℝ := fun n => (dimPol k' B : ℝ) * ((B : ℝ) + n + k') / (((k' : ℝ) - 1) * dimPol k' (B + n))
    with hg
  have hrec : ∀ n, (dimPol k' (B + (n + 1)) : ℝ)
      = dimPol k' (B + n) * ((B : ℝ) + n + 1 + k') / ((B : ℝ) + n + 1) := by
    intro n
    rw [show B + (n + 1) = B + n + 1 by omega, dimPol_succ_eq_real]
    push_cast; ring
  have hstep : ∀ n, (dimPol k' B : ℝ) / dimPol k' (B + n) = g n - g (n + 1) := by
    intro n
    have p0 := dimPol_pos_real k' (B + n)
    simp only [hg]
    rw [hrec n]
    push_cast
    field_simp
    ring
  have hsucc : ∀ n, g (n + 1) * ((B : ℝ) + n + k') = g n * ((B : ℝ) + n + 1) := by
    intro n
    have p0 := dimPol_pos_real k' (B + n)
    simp only [hg]
    rw [hrec n]
    push_cast
    field_simp
    ring
  have hg0 : ∀ n, 0 ≤ g n := by intro n; simp only [hg]; positivity
  have hgzero : g 0 = ((B : ℝ) + k') / ((k' : ℝ) - 1) := by
    simp only [hg]; simp; field_simp
  have hinv : ∀ n, g n * ((B : ℝ) + n + k' - 1) ≤ g 0 * ((B : ℝ) + k' - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      have h1 : g (n + 1) * ((B : ℝ) + (n + 1) + k' - 1) = g n * ((B : ℝ) + n + 1) := by
        rw [← hsucc n]; ring
      rw [h1]
      have : g n * ((B : ℝ) + n + 1) ≤ g n * ((B : ℝ) + n + k' - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (hg0 n)
      linarith
  set C := g 0 * ((B : ℝ) + k' - 1) with hC
  have hbound : ∀ n, g n ≤ C * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : (n : ℝ) + 1 ≤ (B : ℝ) + n + k' - 1 := by
      have : (0 : ℝ) ≤ B := by positivity
      linarith
    rw [mul_one_div, le_div_iff₀ hpos]
    calc g n * ((n : ℝ) + 1) ≤ g n * ((B : ℝ) + n + k' - 1) :=
          mul_le_mul_of_nonneg_left hle (hg0 n)
      _ ≤ C := hinv n
  have htend : Tendsto g atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    rw [mul_zero] at h
    exact squeeze_zero hg0 hbound h
  have hnn : ∀ j, 0 ≤ (dimPol k' B : ℝ) / dimPol k' (B + j) := by
    intro j; have := dimPol_pos_real k' (B + j); positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ n, ∑ i ∈ range n, (dimPol k' B : ℝ) / dimPol k' (B + i) = g 0 - g n := by
    intro n
    rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_range_sub']
  simp_rw [hps]
  rw [← hgzero]
  have := (tendsto_const_nhds (x := g 0)).sub htend
  simpa using this

theorem binomial_series_bound : BinomSeries := by
  intro k' be hk
  exact binomSeries_gen k' be hk

theorem tail_q_bound (k' be : ℕ) (b' : ℝ) (hk : 1 ≤ k') (_hb : 0 < b') :
    ∀ J : ℕ, (be : ℝ) + J + k' ≤ 2 * b' →
      (dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J)
        ≤ ((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b')) := by
  have hk1 : (1 : ℝ) ≤ k' := by exact_mod_cast hk
  have pb := dimPol_pos_real k' be
  intro J
  induction J with
  | zero =>
    intro _
    have e : (dimPol k' be : ℝ) * ((be : ℝ) + k') / dimPol k' be = (be : ℝ) + k' := by
      field_simp
    simpa using e.le
  | succ J ih =>
    intro hJ
    push_cast at hJ ⊢
    have ihJ := ih (by linarith)
    have p0 := dimPol_pos_real k' (be + J)
    have hrec : (dimPol k' (be + (J + 1)) : ℝ)
        = dimPol k' (be + J) * ((be : ℝ) + J + 1 + k') / ((be : ℝ) + J + 1) := by
      rw [show be + (J + 1) = be + J + 1 by omega, dimPol_succ_eq_real]; push_cast; ring
    rw [hrec]
    set q := (dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J) with hq
    have hq0 : 0 ≤ q := by positivity
    have hpos : (0 : ℝ) < (be : ℝ) + J + k' := by positivity
    have hid : (dimPol k' be : ℝ) * ((be : ℝ) + (J + 1) + k')
        / (dimPol k' (be + J) * ((be : ℝ) + J + 1 + k') / ((be : ℝ) + J + 1))
        = q * (((be : ℝ) + J + 1) / ((be : ℝ) + J + k')) := by
      rw [hq]; field_simp; ring
    rw [hid]
    set t := ((be : ℝ) + J + 1) / ((be : ℝ) + J + k') with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ Real.exp (-((k' : ℝ) - 1) / (2 * b')) := by
      have h1 : t = 1 - ((k' : ℝ) - 1) / ((be : ℝ) + J + k') := by rw [ht]; field_simp; ring
      have h2 : ((k' : ℝ) - 1) / (2 * b') ≤ ((k' : ℝ) - 1) / ((be : ℝ) + J + k') :=
        div_le_div_of_nonneg_left (by linarith) hpos (by linarith)
      have h3 := Real.add_one_le_exp (-(((k' : ℝ) - 1) / (2 * b')))
      have h4 : -((k' : ℝ) - 1) / (2 * b') = -(((k' : ℝ) - 1) / (2 * b')) := by ring
      rw [h1, h4]; linarith
    calc q * t ≤ (((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b')))
          * Real.exp (-((k' : ℝ) - 1) / (2 * b')) :=
          mul_le_mul ihJ ht1 ht0 (by positivity)
      _ = ((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * (J + 1) / (2 * b')) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem binomial_tail_bound : BinomTail := by
  intro k' be J La b' hk hb hLa hJ hwin
  have hk2 : 2 ≤ k' := by omega
  have hk5 : (5 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have hs := binomSeries_gen k' (be + J) hk2
  have pJ := dimPol_pos_real k' (be + J)
  have pb := dimPol_pos_real k' be
  have hs2 := hs.mul_left ((dimPol k' be : ℝ) / dimPol k' (be + J))
  have hfun : (fun j : ℕ => (dimPol k' be : ℝ) / dimPol k' (be + J)
      * ((dimPol k' (be + J) : ℝ) / dimPol k' (be + J + j)))
      = fun j => (dimPol k' be : ℝ) / dimPol k' (be + J + j) := by
    funext j; have := dimPol_pos_real k' (be + J + j); field_simp
  rw [hfun] at hs2
  rw [hs2.tsum_eq]
  have hq := tail_q_bound k' be b' (by omega) hb J (by linarith)
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hexp : Real.exp (-((k' : ℝ) - 1) * J / (2 * b')) ≤ Real.exp (-La / 3) := by
    apply Real.exp_le_exp.mpr
    have h1 : La * b' ≤ J * ((k' : ℝ) + 1) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < k' + 1)).mp hJ; linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hJ0 (sub_nonneg.mpr hk5)]
  push_cast
  calc (dimPol k' be : ℝ) / dimPol k' (be + J) * (((be : ℝ) + J + k') / ((k' : ℝ) - 1))
      = ((dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J)) / ((k' : ℝ) - 1) := by ring
    _ ≤ (((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b'))) / ((k' : ℝ) - 1) :=
        div_le_div_of_nonneg_right hq hk1.le
    _ ≤ (((be : ℝ) + k') * Real.exp (-La / 3)) / ((k' : ℝ) - 1) := by
        gcongr
    _ = Real.exp (-La / 3) * (((be : ℝ) + k') / ((k' : ℝ) - 1)) := by ring

theorem dimHar_ratio_ge (k' al be : ℕ) (hk : 2 ≤ k') (hal : 0 < al) :
    1 ≤ (dimHar k' al be : ℝ) / ((dimPol k' al : ℝ) * dimPol k' be)
      * (((be : ℝ) + k') / ((k' : ℝ) - 1)) := by
  have hk2 : (2 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have pa := dimPol_pos_real k' al
  have pb := dimPol_pos_real k' be
  rcases Nat.eq_zero_or_pos be with h0 | hbe
  · subst h0
    have : dimHar k' al 0 = dimPol k' al * dimPol k' 0 := by simp [dimHar]
    rw [this]; push_cast
    rw [div_self (by positivity), one_mul, le_div_iff₀ hk1]; simp
  · obtain ⟨a0, rfl⟩ : ∃ a0, al = a0 + 1 := ⟨al - 1, by omega⟩
    obtain ⟨b0, rfl⟩ : ∃ b0, be = b0 + 1 := ⟨be - 1, by omega⟩
    have hle : dimPol k' a0 * dimPol k' b0 ≤ dimPol k' (a0 + 1) * dimPol k' (b0 + 1) := by
      unfold dimPol
      exact Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
    have hH : dimHar k' (a0 + 1) (b0 + 1)
        = dimPol k' (a0 + 1) * dimPol k' (b0 + 1) - dimPol k' a0 * dimPol k' b0 := by
      simp [dimHar]
    rw [hH, Nat.cast_sub hle]
    push_cast
    have p0 := dimPol_pos_real k' a0
    have p1 := dimPol_pos_real k' b0
    have eX := dimPol_succ_mul_real k' a0
    have eY := dimPol_succ_mul_real k' b0
    set X := (dimPol k' (a0 + 1) : ℝ)
    set Y := (dimPol k' (b0 + 1) : ℝ)
    set x := (dimPol k' a0 : ℝ)
    set y := (dimPol k' b0 : ℝ)
    have hA : (0 : ℝ) < (a0 : ℝ) + 1 := by positivity
    have hB0 : (0 : ℝ) ≤ (b0 : ℝ) := by positivity
    have hXx : x ≤ X := by
      have : x * ((a0 : ℝ) + 1) ≤ X * ((a0 : ℝ) + 1) := by
        rw [eX]; nlinarith
      exact le_of_mul_le_mul_right this hA
    rw [div_mul_div_comm, one_le_div (by positivity)]
    have hYB : 0 ≤ Y * ((b0 : ℝ) + 1) := by positivity
    have h1 : x * (Y * ((b0 : ℝ) + 1)) ≤ X * (Y * ((b0 : ℝ) + 1)) := mul_le_mul_of_nonneg_right hXx hYB
    have hXY : 0 ≤ X * Y := by positivity
    nlinarith

theorem density_lower_bound : DensityLower := by
  intro k' al be La b' hk hal hb hLa hwin
  set J0 : ℝ := La * b' / (k' + 1) with hJ0
  set N : ℕ := ⌊J0⌋₊ + 1 with hN
  have hk2 : 2 ≤ k' := by omega
  have hk5 : (5 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have hal' : (0 : ℝ) < al := by exact_mod_cast hal
  have hJ00 : 0 ≤ J0 := by positivity
  have he0 : 0 ≤ 1 - Real.exp (-La / 3) := by
    have : Real.exp (-La / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have pa := dimPol_pos_real k' al
  have pb := dimPol_pos_real k' be
  have hH0 : (0 : ℝ) ≤ dimHar k' al be := by positivity
  set h : ℝ := (dimHar k' al be : ℝ) / ((dimPol k' al : ℝ) * dimPol k' be) with hh
  have hh0 : 0 ≤ h := by positivity
  have hhS := dimHar_ratio_ge k' al be hk2 hal
  set S : ℝ := ((be : ℝ) + k') / ((k' : ℝ) - 1) with hS
  set f : ℕ → ℝ := fun j => (dimPol k' be : ℝ) / dimPol k' (be + j) with hf
  have hser : HasSum f S := binomSeries_gen k' be hk2
  have hNJ : J0 ≤ (N : ℝ) := by rw [hN]; push_cast; exact (Nat.lt_floor_add_one J0).le
  have htail := binomial_tail_bound k' be N La b' hk hb hLa hNJ hwin
  have hsplit := hser.summable.sum_add_tsum_nat_add N
  have htail' : ∑' i, f (i + N) = ∑' j : ℕ, (dimPol k' be : ℝ) / dimPol k' (be + N + j) := by
    congr 1; funext i; simp only [hf]; rw [show be + (i + N) = be + N + i by omega]
  rw [hser.tsum_eq, htail'] at hsplit
  have hpart : S * (1 - Real.exp (-La / 3)) ≤ ∑ j ∈ range N, f j := by
    have : Real.exp (-La / 3) * S = S * Real.exp (-La / 3) := by ring
    nlinarith [htail]
  by_cases ha : 1 - (k' : ℝ) * J0 / al ≤ 0
  · have : (0 : ℝ) ≤ ∑ j ∈ range N,
        (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j)) := by
      apply Finset.sum_nonneg; intro j _
      have := dimPol_pos_real k' (al + j); have := dimPol_pos_real k' (be + j); positivity
    nlinarith [mul_nonneg (neg_nonneg.mpr ha) he0]
  · rw [not_le] at ha
    set a := 1 - (k' : ℝ) * J0 / al with hadef
    have hterm : ∀ j ∈ range N, h * a * f j
        ≤ (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j)) := by
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      have hjJ : (j : ℝ) ≤ J0 := by
        have : j ≤ ⌊J0⌋₊ := by omega
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le hJ00)
      have hr := binomial_ratio_bound k' al j hal
      have hra : a ≤ (dimPol k' al : ℝ) / dimPol k' (al + j) := by
        refine le_trans ?_ hr
        have : (k' : ℝ) * j / al ≤ (k' : ℝ) * J0 / al := by gcongr
        linarith
      have p1 := dimPol_pos_real k' (al + j)
      have p2 := dimPol_pos_real k' (be + j)
      have heq : (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j))
          = h * ((dimPol k' al : ℝ) / dimPol k' (al + j)) * f j := by
        simp only [hh, hf]; field_simp
      rw [heq]
      have hf0 : 0 ≤ f j := by simp only [hf]; positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hra hh0) hf0
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have h1 : h * a * (S * (1 - Real.exp (-La / 3))) ≤ h * a * ∑ j ∈ range N, f j :=
      mul_le_mul_of_nonneg_left hpart (by positivity)
    have h2 : a * (1 - Real.exp (-La / 3)) ≤ h * a * (S * (1 - Real.exp (-La / 3))) := by
      have e : h * a * (S * (1 - Real.exp (-La / 3))) = (h * S) * (a * (1 - Real.exp (-La / 3))) := by
        ring
      rw [e]
      have hae : 0 ≤ a * (1 - Real.exp (-La / 3)) := mul_nonneg ha.le he0
      nlinarith
    linarith

end Formalism.CountingSumsFrames
