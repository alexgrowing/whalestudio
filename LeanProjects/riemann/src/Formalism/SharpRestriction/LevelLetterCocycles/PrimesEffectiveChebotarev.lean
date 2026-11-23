import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.ResidualIrreducibleOfTheoremThreePrime
import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple
import Formalism.PadicSubsetSums.StableGradedCounts.PropositionOneCentralCount
import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight
import Formalism.PadicSubsetSums.StableGradedCounts.TWCentralIdempotentIntegral
import Formalism.SharpRestriction.LevelLetterCocycles.PrimesOverLiterature.RayPrimeCountAllToSquarefree

noncomputable section

namespace Formalism.MainNotions.N.CuspidalLatticeIdempotents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped ComplexOrder

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem algBB_sub (g N : ℕ) (hg : 2 ≤ g) :
    Formalism.CyclotomicNorms.BB N g ⊆ ((Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BB g N : Finset ℕ) : Set ℕ) := by
  intro l hl
  rw [Finset.mem_coe, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_BB_iff]
  rcases hl with h | ⟨d, hd1, hdN, hlp, hlt⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, hlp, d, Finset.mem_Icc.mpr ⟨hd1, hdN⟩, hlt⟩
    have hone : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
    have hv : padicValNat l (g ^ d - 1) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, pow_zero] at hlt
      omega
    have hdvd : l ∣ g ^ d - 1 := by
      by_contra hnd
      exact hv (padicValNat.eq_zero_of_not_dvd hnd)
    have h1 := Nat.le_of_dvd (by omega) hdvd
    have h2 : g ^ d ≤ g ^ N := Nat.pow_le_pow_right (by omega) hdN
    omega

private theorem four_dvd_QS (D : D7) : 4 ∣ D.host.QS :=
  dvd_trans ⟨2 ^ D.R.e, by show 2 ^ (D.R.e + 2) = 4 * 2 ^ D.R.e; ring⟩ D.host.tower_dvd

theorem cond_ge_four (D : D7) : (4 : ℝ) ≤ (D.ntypes.cond : ℝ) := by
  have hc : D.ntypes.cond = D.host.QS * D.host.q * D.host.d := rfl
  have hn : 4 ≤ D.host.QS := Nat.le_of_dvd D.host.QS_pos (four_dvd_QS D)
  have hq : 1 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have : 4 ≤ D.ntypes.cond := by
    rw [hc]
    calc 4 = 4 * 1 * 1 := by norm_num
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  exact_mod_cast this

theorem r_ge_six (D : D7) : 6 ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  show 6 ≤ D.R.k + D.R.m - 1
  omega

theorem cubic_bound_twenty (N y : ℝ) (hN : 1 ≤ N) (hy : 1 ≤ y) :
    (3 * N + 1) * (1 + 2 * N ^ 2 * (y + 1)) ≤ 20 * N ^ 3 * y := by
  have ha : 3 * N + 1 ≤ 4 * N := by linarith
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have hNy : N ^ 2 ≤ N ^ 2 * y := le_mul_of_one_le_right (by positivity) hy
  have hb : 1 + 2 * N ^ 2 * (y + 1) ≤ 5 * (N ^ 2 * y) := by nlinarith
  calc (3 * N + 1) * (1 + 2 * N ^ 2 * (y + 1)) ≤ (4 * N) * (5 * (N ^ 2 * y)) :=
        mul_le_mul ha hb (by positivity) (by positivity)
    _ = 20 * N ^ 3 * y := by ring

theorem two_of_count (D : D7) (Y : ℝ) (hY1 : 1 ≤ Y)
    (hcount : 20 * (D.R.r : ℝ) ^ 3 * Y ^ ((3 : ℝ) / 4) < (ArithmeticCylinders.admissiblePrimesDyadic D Y : ℝ)) :
    ∃ g₁ g₂ : ℕ, D.ntypes.admissible g₁ ∧ D.ntypes.admissible g₂ ∧
      Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
      g₁ ≠ g₂ ∧ Disjoint (Formalism.CyclotomicNorms.BB D.R.r g₁) (Formalism.CyclotomicNorms.BB D.R.r g₂) := by
  classical
  have hr1 : 1 ≤ D.R.r := by have := r_ge_six D; omega
  have hN1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hr1
  have hy1 : 1 ≤ Y ^ ((3 : ℝ) / 4) := Real.one_le_rpow hY1 (by norm_num)
  have hmain : (3 * (D.R.r : ℝ) + 1) * (1 + 2 * (D.R.r : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) <
      (ArithmeticCylinders.admissiblePrimesDyadic D Y : ℝ) :=
    lt_of_le_of_lt (cubic_bound_twenty (D.R.r : ℝ) (Y ^ ((3 : ℝ) / 4)) hN1 hy1) hcount
  let P : Finset ℕ := (Finset.range (⌊2 * Y⌋₊ + 1)).filter
    (fun p => D.ntypes.admissible p ∧ Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y)
  have hmem : ∀ p, p ∈ P ↔ D.ntypes.admissible p ∧ Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y := by
    intro p
    simp only [P, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor h.2.2), h⟩
  have hcardP : ArithmeticCylinders.admissiblePrimesDyadic D Y = P.card := by
    unfold ArithmeticCylinders.admissiblePrimesDyadic
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun p => (hmem p).symm)), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  rw [hcardP] at hmain
  obtain ⟨g₁, hg₁, g₂, hg₂, hne, hdisj⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.proposition_one_central_count D.R.r Y P hr1 hY1
    (fun g hg => ⟨((hmem g).1 hg).1.1, ((hmem g).1 hg).2.1, ((hmem g).1 hg).2.2⟩) hmain
  obtain ⟨ha₁, hY₁, h2Y₁⟩ := (hmem g₁).1 hg₁
  obtain ⟨ha₂, hY₂, h2Y₂⟩ := (hmem g₂).1 hg₂
  refine ⟨g₁, g₂, ha₁, ha₂, hY₁, h2Y₁, hY₂, h2Y₂, hne, ?_⟩
  exact (Finset.disjoint_coe.mpr hdisj).mono (algBB_sub g₁ D.R.r ha₁.1.two_le)
    (algBB_sub g₂ D.R.r ha₂.1.two_le)

theorem dyadic_count (P : ℕ → Prop) [DecidablePred P] (X : ℝ) (J : ℕ) :
    ((Finset.range (⌊X⌋₊ + 1)).filter (fun p => P p ∧ (p : ℝ) ≤ X)).card ≤
      ((Finset.range (⌊X⌋₊ + 1)).filter (fun p => P p ∧ (p : ℝ) ≤ X / 2 ^ J)).card +
      ∑ j ∈ Finset.range J, ((Finset.range (⌊X⌋₊ + 1)).filter
        (fun p => P p ∧ X / 2 ^ (j + 1) ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * (X / 2 ^ (j + 1)))).card := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have e : 2 * (X / 2 ^ (J + 1)) = X / 2 ^ J := by rw [pow_succ]; field_simp
    have hsub : (Finset.range (⌊X⌋₊ + 1)).filter (fun p => P p ∧ (p : ℝ) ≤ X / 2 ^ J) ⊆
        (Finset.range (⌊X⌋₊ + 1)).filter (fun p => P p ∧ (p : ℝ) ≤ X / 2 ^ (J + 1)) ∪
        (Finset.range (⌊X⌋₊ + 1)).filter
          (fun p => P p ∧ X / 2 ^ (J + 1) ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * (X / 2 ^ (J + 1))) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_union] at hp ⊢
      obtain ⟨hr, hPp, hle⟩ := hp
      by_cases h : (p : ℝ) ≤ X / 2 ^ (J + 1)
      · exact Or.inl ⟨hr, hPp, h⟩
      · exact Or.inr ⟨hr, hPp, le_of_lt (not_le.mp h), by rw [e]; exact hle⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega

theorem geom_half (X : ℝ) (J : ℕ) : ∑ j ∈ Finset.range J, X / 2 ^ (j + 1) = X - X / 2 ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    field_simp
    ring

theorem dyadic_select (D : D7) (X κ : ℝ) (J : ℕ) (hX : 0 < X) (hκ : 0 < κ)
    (hlow2t : X / 2 ^ J < 2 * (X * κ)) (hA8 : 8 * (X * κ) ≤ (ArithmeticCylinders.admissiblePrimesLE D X : ℝ)) :
    ∃ j ∈ Finset.range J, X / 2 ^ (j + 1) * κ ≤ (ArithmeticCylinders.admissiblePrimesDyadic D (X / 2 ^ (j + 1)) : ℝ) := by
  classical
  have ht0 : 0 < X * κ := mul_pos hX hκ
  have h2J : (0 : ℝ) < 2 ^ J := by positivity
  let R := Finset.range (⌊X⌋₊ + 1)
  have hdy := dyadic_count D.ntypes.admissible X J
  have hall : ArithmeticCylinders.admissiblePrimesLE D X = (R.filter (fun p => D.ntypes.admissible p ∧ (p : ℝ) ≤ X)).card := by
    have hm : ∀ p, p ∈ R.filter (fun p => D.ntypes.admissible p ∧ (p : ℝ) ≤ X) ↔
        D.ntypes.admissible p ∧ (p : ℝ) ≤ X := by
      intro p
      simp only [R, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨Nat.lt_succ_of_le (Nat.le_floor h.2), h⟩
    unfold ArithmeticCylinders.admissiblePrimesLE
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun p => (hm p).symm)), Nat.card_eq_fintype_card, Fintype.card_coe]
  have hlowc : ((R.filter (fun p => D.ntypes.admissible p ∧ (p : ℝ) ≤ X / 2 ^ J)).card : ℝ) ≤ X / 2 ^ J := by
    have hsub : R.filter (fun p => D.ntypes.admissible p ∧ (p : ℝ) ≤ X / 2 ^ J) ⊆ Finset.Icc 1 ⌊X / 2 ^ J⌋₊ := by
      intro p hp
      simp only [R, Finset.mem_filter] at hp
      simp only [Finset.mem_Icc]
      exact ⟨hp.2.1.1.one_lt.le, Nat.le_floor hp.2.2⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    calc ((R.filter _).card : ℝ) ≤ (⌊X / 2 ^ J⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ X / 2 ^ J := Nat.floor_le (by positivity)
  have hwin : ∀ j, ((R.filter (fun p => D.ntypes.admissible p ∧ X / 2 ^ (j + 1) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ 2 * (X / 2 ^ (j + 1)))).card) = ArithmeticCylinders.admissiblePrimesDyadic D (X / 2 ^ (j + 1)) := by
    intro j
    have h2 : 2 * (X / 2 ^ (j + 1)) ≤ X := by
      rw [pow_succ, ← div_div, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      exact div_le_self hX.le (one_le_pow₀ (by norm_num))
    have hm : ∀ p, p ∈ R.filter (fun p => D.ntypes.admissible p ∧ X / 2 ^ (j + 1) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ 2 * (X / 2 ^ (j + 1))) ↔
        D.ntypes.admissible p ∧ X / 2 ^ (j + 1) ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * (X / 2 ^ (j + 1)) := by
      intro p
      simp only [R, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨Nat.lt_succ_of_le (Nat.le_floor (h.2.2.trans h2)), h⟩
    unfold ArithmeticCylinders.admissiblePrimesDyadic
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun p => (hm p).symm)), Nat.card_eq_fintype_card, Fintype.card_coe]
  by_contra hcon
  push Not at hcon
  have hsum : (∑ j ∈ Finset.range J, ((R.filter (fun p => D.ntypes.admissible p ∧ X / 2 ^ (j + 1) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ 2 * (X / 2 ^ (j + 1)))).card : ℝ)) ≤ X * κ := by
    calc (∑ j ∈ Finset.range J, ((R.filter (fun p => D.ntypes.admissible p ∧ X / 2 ^ (j + 1) ≤ (p : ℝ) ∧
            (p : ℝ) ≤ 2 * (X / 2 ^ (j + 1)))).card : ℝ))
        ≤ ∑ j ∈ Finset.range J, X / 2 ^ (j + 1) * κ := by
          apply Finset.sum_le_sum
          intro j hj
          rw [hwin j]
          exact (hcon j hj).le
      _ = (X - X / 2 ^ J) * κ := by rw [← Finset.sum_mul, geom_half]
      _ ≤ X * κ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : 0 ≤ X / 2 ^ J := by positivity
          linarith
  have hdyR : (ArithmeticCylinders.admissiblePrimesLE D X : ℝ) ≤ ((R.filter (fun p => D.ntypes.admissible p ∧ (p : ℝ) ≤ X / 2 ^ J)).card : ℝ) +
      ∑ j ∈ Finset.range J, ((R.filter (fun p => D.ntypes.admissible p ∧ X / 2 ^ (j + 1) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ 2 * (X / 2 ^ (j + 1)))).card : ℝ) := by
    rw [hall]; exact_mod_cast hdy
  linarith

theorem baseChange_preserves_unitary_of (D : D7) (c₀ c₂ c₁ : ℝ) (h0 : 0 < c₀) (h1 : 2 ^ 14 / c₀ ≤ c₁) (h2 : c₂ ≤ c₁)
    (hM : ArithmeticCylinders.MrayRay D 1) (hP : ArithmeticCylinders.adm2 D c₀ c₂) : ArithmeticCylinders.Conclusion1 D c₁ := by
  classical
  intro X hX hc1 hd1 hr21 hH1 hH2
  have hc4 : (4 : ℝ) ≤ (D.ntypes.cond : ℝ) := cond_ge_four D
  have hc4N : 4 ≤ D.ntypes.cond := by exact_mod_cast hc4
  set c : ℝ := (D.ntypes.cond : ℝ) with hcdef
  have hc0 : 0 < c := by linarith
  have hcne : c ≠ 0 := hc0.ne'
  have hc1' : 1 ≤ c := by linarith
  have hN21 : (21 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hr21
  set N : ℝ := (D.R.r : ℝ) with hNdef
  set t : ℝ := X * c ^ (-(20 : ℝ)) with htdef
  have hc20 : c ^ (-(20 : ℝ)) = (c ^ 20)⁻¹ := by rw [Real.rpow_neg hc0.le]; norm_cast
  have ht0 : 0 < t := by rw [htdef, hc20]; positivity
  have hXt : X = t * c ^ 20 := by rw [htdef, hc20]; field_simp
  set B : ℝ := N ^ 4 * c ^ 500 with hBdef
  have hN1 : 1 ≤ N := by linarith
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) (one_le_pow₀ hc1')
  have htq : (t ^ (1 / 4 : ℝ)) ^ 4 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have htB : B ^ 4 ≤ t := by
    have := pow_le_pow_left₀ (by positivity) hH1 4
    rwa [htq] at this
  have ht1 : 1 ≤ t := le_trans (one_le_pow₀ hB1) htB
  have hX1737 : c ^ 1737 ≤ X := by
    have hcB : c ^ 2000 ≤ B ^ 4 := by
      have : c ^ 500 ≤ B := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hN1)
      calc c ^ 2000 = (c ^ 500) ^ 4 := by ring
        _ ≤ B ^ 4 := pow_le_pow_left₀ (by positivity) this 4
    calc c ^ 1737 ≤ c ^ 2020 := pow_le_pow_right₀ hc1' (by norm_num)
      _ = c ^ 2000 * c ^ 20 := by ring
      _ ≤ t * c ^ 20 := mul_le_mul_of_nonneg_right (hcB.trans htB) (by positivity)
      _ = X := hXt.symm
  have hX1 : 1 < X := lt_of_lt_of_le (one_lt_pow₀ (by linarith) (by norm_num)) hX1737
  have hlog : 0 < Real.log X := Real.log_pos hX1

  have hA := hP hM (le_trans h2 hd1) X hX1737
  have hA8 : 8 * t ≤ (ArithmeticCylinders.admissiblePrimesLE D X : ℝ) := by
    refine le_trans ?_ hA
    have hc₀c : 2 ^ 14 ≤ c₀ * c := by
      have := h1.trans hc1
      rw [div_le_iff₀ h0] at this
      linarith
    have step1 : c₀ / 2 * ((4 * c ^ 3) ^ 5)⁻¹ * X / (c ^ 3 * c) ≤
        c₀ / 2 * ((4 * c ^ 3) ^ 5)⁻¹ * X / (c ^ 3 * Real.log X) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hH2 (by positivity)
    refine le_trans ?_ step1
    have e : c₀ / 2 * ((4 * c ^ 3) ^ 5)⁻¹ * X / (c ^ 3 * c) = c₀ * c * t / 2 ^ 11 := by
      rw [hXt]; field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hc₀c ht0.le]

  set M : ℕ := D.ntypes.cond ^ 20 with hMdef
  have hM2 : 2 ≤ M := by
    calc 2 ≤ 4 ^ 20 := by norm_num
      _ ≤ D.ntypes.cond ^ 20 := Nat.pow_le_pow_left hc4N 20
  set J : ℕ := Nat.log 2 M with hJdef
  have hJ1 : 1 ≤ J := Nat.log_pos (by norm_num) hM2
  have hJle : 2 ^ J ≤ M := Nat.pow_log_le_self 2 (by omega)
  have hJlt : M < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  have hMc : (M : ℝ) = c ^ 20 := by rw [hMdef]; push_cast; rfl
  have hJleR : (2 : ℝ) ^ J ≤ c ^ 20 := by rw [← hMc]; exact_mod_cast hJle
  have hJltR : c ^ 20 < (2 : ℝ) ^ (J + 1) := by rw [← hMc]; exact_mod_cast hJlt
  have h2J : (0 : ℝ) < 2 ^ J := by positivity
  have hlowt : t ≤ X / 2 ^ J := by
    rw [hXt, le_div_iff₀ h2J]
    exact mul_le_mul_of_nonneg_left hJleR ht0.le
  have hlow2t : X / 2 ^ J < 2 * t := by
    rw [hXt, div_lt_iff₀ h2J]
    have : c ^ 20 < 2 * 2 ^ J := by
      have h' := hJltR
      rw [pow_succ (2 : ℝ) J] at h'
      linarith
    nlinarith
  obtain ⟨j, hj, hcnt⟩ := dyadic_select D X (c ^ (-(20 : ℝ))) J hX (Real.rpow_pos_of_pos hc0 _) hlow2t hA8
  have hjJ : j + 1 ≤ J := Finset.mem_range.mp hj
  set Y : ℝ := X / 2 ^ (j + 1) with hYdef
  have hYt : t ≤ Y := by
    refine le_trans hlowt ?_
    rw [hYdef]
    exact div_le_div_of_nonneg_left hX.le (by positivity) (pow_le_pow_right₀ (by norm_num) hjJ)
  have hYX : Y ≤ X / 2 := by
    rw [hYdef]
    exact div_le_div_of_nonneg_left hX.le (by norm_num) (by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega))
  have hY0 : 0 < Y := lt_of_lt_of_le ht0 hYt
  have hY1 : 1 ≤ Y := le_trans ht1 hYt

  have hYq : B ≤ Y ^ (1 / 4 : ℝ) := le_trans hH1 (Real.rpow_le_rpow ht0.le hYt (by norm_num))
  have hB20 : 20 * N ^ 3 * c ^ 20 < B := by
    have hc500 : c ^ 20 ≤ c ^ 500 := pow_le_pow_right₀ hc1' (by norm_num)
    have hN3 : 0 < N ^ 3 * c ^ 20 := by positivity
    calc 20 * N ^ 3 * c ^ 20 < 21 * (N ^ 3 * c ^ 20) := by nlinarith
      _ ≤ N * (N ^ 3 * c ^ 20) := mul_le_mul_of_nonneg_right hN21 hN3.le
      _ = N ^ 4 * c ^ 20 := by ring
      _ ≤ N ^ 4 * c ^ 500 := mul_le_mul_of_nonneg_left hc500 (by positivity)
  have hsplit : Y = Y ^ ((3 : ℝ) / 4) * Y ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hY0]; norm_num
  have hcount : 20 * N ^ 3 * Y ^ ((3 : ℝ) / 4) < (ArithmeticCylinders.admissiblePrimesDyadic D Y : ℝ) := by
    refine lt_of_lt_of_le ?_ hcnt
    have hy0 : 0 < Y ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hY0 _
    rw [hc20]
    have key : 20 * N ^ 3 * c ^ 20 < Y ^ (1 / 4 : ℝ) := lt_of_lt_of_le hB20 hYq
    have : 20 * N ^ 3 * Y ^ ((3 : ℝ) / 4) * c ^ 20 < Y :=
      calc 20 * N ^ 3 * Y ^ ((3 : ℝ) / 4) * c ^ 20 = Y ^ ((3 : ℝ) / 4) * (20 * N ^ 3 * c ^ 20) := by ring
        _ < Y ^ ((3 : ℝ) / 4) * Y ^ (1 / 4 : ℝ) := mul_lt_mul_of_pos_left key hy0
        _ = Y := hsplit.symm
    rw [← div_eq_mul_inv, lt_div_iff₀ (by positivity)]
    exact this
  obtain ⟨g₁, g₂, hg⟩ := two_of_count D Y hY1 hcount
  exact ⟨Y, hYt, hYX, ⟨g₁, g₂, hg⟩, hcnt⟩

def CountQ (D : D7) (a : ℕ) (C ε' : ℝ) : Prop :=
  ArithmeticCylinders.MrayRay D a →
  ∀ Y : ℝ, 1 ≤ Y → C * Real.log (D.ntypes.cond : ℝ) ^ 2 ≤ Real.log Y →
    Y ^ (1 - ε') ≤ (ArithmeticCylinders.admissiblePrimesDyadic D Y : ℝ)

end Formalism.MainNotions.N.CuspidalLatticeIdempotents
