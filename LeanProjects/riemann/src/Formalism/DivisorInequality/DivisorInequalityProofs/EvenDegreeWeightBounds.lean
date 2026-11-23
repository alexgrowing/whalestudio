import Mathlib
import Formalism.DivisorInequality.DivIneqTopAnchorU
import Formalism.DivisorInequality.DivisorInequalityProofs.BaseLevelBoundsWithCovolumeHolds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramTopExact

open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder

namespace Formalism.DivisorInequality

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)

namespace UniformCovolumeTail

theorem cvE (Cb ce X B0 l2 Nc : ℝ) (hX : 0 < X) :
    Cb * (ce * X) * (B0 + l2 * Nc / X) = Cb * (ce * (X * B0 + l2 * Nc)) := by
  have e : X * X⁻¹ = 1 := mul_inv_cancel₀ hX.ne'
  linear_combination (Cb * ce * l2 * Nc) * e

end UniformCovolumeTail

namespace UniformCovolumeTail

set_option maxHeartbeats 800000 in

theorem stepDiSharp (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' hK : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 Ce Ch : ℝ)
    (h32 : ∀ j s, logK j s ≤
      (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j)))
    (hmean : ∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ))
    (hOm : ∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm)
    (hSK : ∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT) + Ce * f * N ^ 2 * logg)
    (hth : (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L)
    (hh : ∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg))
    (hh' : ∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg))
    (hcard : (Fintype.card Pl : ℝ) ≤ f) (hg0 : ∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hL : 0 ≤ L) (hLLa : L ≤ La) (hLa1 : 1 ≤ La)
    (h5 : ∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La)
    (h6 : ∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La)
    (hT : logT ≤ C7 * m * L) (hg : logg ≤ C8 * L)
    (p2 : 0 ≤ C2) (p3 : 0 ≤ C3) (p4 : 0 ≤ C4) (p5 : 0 ≤ c5) (p6 : 0 ≤ c6) (p7 : 0 ≤ C7) (p8 : 0 ≤ C8)
    (pe : 0 ≤ Ce)
    (kA : C3 + c5 + 2 * c6 + 1 + 2 * C4 + 2 * Ce * C8 ≤ Ch) (kB : 2 * (C2 + C4) * (C7 + C8) ≤ Ch) :
    ∀ j, hK j ≤ ∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm) +
      Ch * f * N ^ 2 * (La + m ^ 3 * L) := by
  intro j
  have hn : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hc0 : 0 ≤ (Fintype.card Pl : ℝ) * g0 j := mul_nonneg (Nat.cast_nonneg _) (hg0 j).1
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hcard
  have hLa0 : 0 ≤ La := by linarith
  have hN2 : 1 ≤ N ^ 2 := by
    have := mul_le_mul hN hN zero_le_one (by linarith)
    linarith only [this]
  have hF0 : 0 ≤ f * N ^ 2 := mul_nonneg hf0 (sq_nonneg N)
  have hcF : (Fintype.card Pl : ℝ) * g0 j ≤ f * N ^ 2 := mul_le_mul hcard (hg0 j).2 (hg0 j).1 hf0

  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 =
      (Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT) + Ce * f * N ^ 2 * logg) +
        (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) + (logh j + logh' j) := ⟨_, rfl⟩
  have hpt : ∀ s, logK j s ≤ (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s + K0 := by
    intro s
    have a1 := h32 j s
    have a2 := hSK j s
    linarith
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset Emb)) => hpt s)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum

  have hX : ∑ s, (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) =
      (Fintype.card Emb : ℝ) * ∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    have e := hOm τ
    rw [div_eq_iff hn.ne'] at e
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, e]
    ring
  rw [hX] at hsum

  have hZ : (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) ≤
      f * (1 + 2 * N ^ 2 * (c6 * La)) := by
    calc (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2)))
        ≤ ∑ _τ : Pl, (1 + 2 * N ^ 2 * (c6 * La)) := by
          apply Finset.sum_le_sum
          intro τ _
          have a1 := mul_le_mul_of_nonneg_left (h6 j τ) (hg0 j).1
          have a2 := mul_le_mul_of_nonneg_right (hg0 j).2 (mul_nonneg p6 hLa0)
          linarith
      _ = (Fintype.card Pl : ℝ) * (1 + 2 * N ^ 2 * (c6 * La)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ f * (1 + 2 * N ^ 2 * (c6 * La)) :=
          mul_le_mul_of_nonneg_right hcard
            (add_nonneg zero_le_one (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg N)) (mul_nonneg p6 hLa0)))

  have hscal : K0 + (Fintype.card Pl : ℝ) * g0 j * (C3 * L) ≤ Ch * f * N ^ 2 * (La + m ^ 3 * L) := by
    have b1 := mul_le_mul_of_nonneg_left (h5 j) hc0
    have b2 := mul_le_mul_of_nonneg_right hcF (mul_nonneg p5 hLa0)
    have b3 := mul_le_mul_of_nonneg_right hcF (mul_nonneg p3 hL)
    have b4 : C2 * f * m ^ 2 * N ^ 2 * (logg + logT) ≤ C2 * f * m ^ 2 * N ^ 2 * (C8 * L + C7 * m * L) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg (mul_nonneg p2 hf0) (sq_nonneg m)) (sq_nonneg N))
    have b5 : Ce * f * N ^ 2 * logg ≤ Ce * f * N ^ 2 * (C8 * L) :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg (mul_nonneg pe hf0) (sq_nonneg N))
    have b6 := hh j
    have b7 := hh' j
    have b8 : 2 * C4 * (f * N ^ 2) * (L + logT + logg) ≤ 2 * C4 * (f * N ^ 2) * (L + C7 * m * L + C8 * L) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg zero_le_two p4) hF0)
    have q1 : (1 : ℝ) * 1 ≤ N ^ 2 * La := mul_le_mul hN2 hLa1 zero_le_one (sq_nonneg N)
    have q2 := mul_le_mul_of_nonneg_left q1 hf0
    have hm1 : 1 ≤ m ^ 2 := by
      have := mul_le_mul hm hm zero_le_one (by linarith)
      linarith only [this]
    have hm2 : m ^ 2 ≤ m ^ 3 := by
      have := mul_le_mul_of_nonneg_left hm (sq_nonneg m)
      linarith only [this]
    have hm3 : m ≤ m ^ 3 := by
      have := mul_le_mul_of_nonneg_left hm1 (by linarith : (0 : ℝ) ≤ m)
      linarith only [this]
    have hm4 : 1 ≤ m ^ 3 := le_trans hm hm3
    have e1 : 0 ≤ f * N ^ 2 * C3 * (La - L) := mul_nonneg (mul_nonneg hF0 p3) (by linarith)
    have e2 : 0 ≤ f * N ^ 2 * C4 * (La - L) := mul_nonneg (mul_nonneg hF0 p4) (by linarith)
    have e3 : 0 ≤ f * N ^ 2 * (Ce * C8) * (La - L) :=
      mul_nonneg (mul_nonneg hF0 (mul_nonneg pe p8)) (by linarith)
    have e5 : 0 ≤ f * N ^ 2 * (C2 * C8) * ((m ^ 3 - m ^ 2) * L) :=
      mul_nonneg (mul_nonneg hF0 (mul_nonneg p2 p8)) (mul_nonneg (by linarith) hL)
    have e6 : 0 ≤ f * N ^ 2 * (C4 * C7) * ((m ^ 3 - m) * L) :=
      mul_nonneg (mul_nonneg hF0 (mul_nonneg p4 p7)) (mul_nonneg (by linarith) hL)
    have e7 : 0 ≤ f * N ^ 2 * (C4 * C8) * ((m ^ 3 - 1) * L) :=
      mul_nonneg (mul_nonneg hF0 (mul_nonneg p4 p8)) (mul_nonneg (by linarith) hL)
    have e8 : f * N ^ 2 * ((C3 + c5 + 2 * c6 + 1 + 2 * C4 + 2 * Ce * C8) * La) ≤ f * N ^ 2 * (Ch * La) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right kA hLa0) hF0
    have e9 : f * N ^ 2 * ((2 * (C2 + C4) * (C7 + C8)) * (m ^ 3 * L)) ≤ f * N ^ 2 * (Ch * (m ^ 3 * L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right kB (mul_nonneg (by linarith) hL)) hF0
    rw [hK0]
    linarith
  rw [hmean j, div_le_iff₀ hn]
  have hth' := (div_le_iff₀ hn).mp hth
  have t1 := mul_le_mul_of_nonneg_left hth' hc0
  have t2 := mul_le_mul_of_nonneg_left hscal hn.le
  linarith

end UniformCovolumeTail

set_option maxHeartbeats 800000 in

theorem height_bound_at_set : HeightS := by
  intro J Pl Emb _ _ _ _ TT _ nr hu hP mlam logT hK aT logH Ch nV L' ν x eps L b a rd La m f k N S η b'
    logOm g0 logK MainNotions logOmτ logth0 logh logh' v logg C2 Cth C4 c5 c6 CT C8 Ce ev bT nτ lam1 D0 D1
    logc logxi Cev hhu hL6 h32 hmean hOm hSK hth hh hh' hg0 h5 h6 hg p2 pth p4 p5 p6 p8 pe hPb hlogc
    hlogxi hnτ hlam hlam' hD0 hD1 hbT hT0 hT pT pb' hev pev hx heps hLdef hb ha hrd hLa hcard hm hf hk
    hkmN hS hη kC kA kB
  have hN : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    exact Real.one_le_rpow hx heps.le
  have hL0 : 0 ≤ L := by linarith
  have hx0 : 0 < x := by linarith
  have hrd0 : 0 < rd := by linarith
  have hloga : Real.log a = Real.log x + L := by
    rw [ha, hb, Real.log_mul hx0.ne' (Real.exp_pos L).ne', Real.log_exp]
  have ha0 : 0 < a := by
    rw [ha, hb]
    exact mul_pos hx0 (Real.exp_pos L)
  have hLa' : La = Real.log x + L + Real.log rd := by
    rw [hLa, Real.log_mul ha0.ne' hrd0.ne', hloga]
  have lx : 0 ≤ Real.log x := Real.log_nonneg hx
  have lrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hLLa : L ≤ La := by linarith
  have hLa1 : 1 ≤ La := by linarith
  have hLa0 : 0 ≤ La := by linarith
  have hl2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos two_pos
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have h2a : Real.log (2 * a) = Real.log 2 + Real.log a := Real.log_mul two_ne_zero ha0.ne'
  have hℓ : Real.log (2 * a) ≤ 2 * La := by linarith
  have hℓ0 : 0 ≤ Real.log (2 * a) := by linarith
  have hmN : m ≤ N := by linarith
  have hTN : logT ≤ CT * N * La := by
    have q1 : m * L ≤ N * La := mul_le_mul hmN hLLa hL0 hN0
    have q2 := mul_le_mul_of_nonneg_left q1 pT
    linarith
  have hT0' : 0 ≤ CT * N * La := mul_nonneg (mul_nonneg pT hN0) hLa0
  have hmη0 : 0 ≤ m * η := mul_nonneg (by linarith) hη
  have hmη : η ≤ m * η := by
    have := mul_le_mul_of_nonneg_right hm hη
    linarith

  have hK' := UniformCovolumeTail.stepDiSharp J Pl Emb nr ν g0 logK MainNotions logOmτ logth0 logh logh' hK logOm v f m N L La
    logT logg C2 Cth C4 c5 c6 CT C8 Ce Ch h32 hmean hOm hSK hth hh hh' hcard hg0 hm hN hL0 hLLa hLa1
    h5 h6 hT hg p2 pth p4 p5 p6 pT p8 pe kA kB
  have hsK := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) => hK' j)

  have hTT : (Finset.univ.filter (· ∈ TT)) = TT := by
    ext τ
    simp
  have hite : ∀ g : Pl → ℝ, ∑ τ, (if τ ∈ TT then g τ else 0) = ∑ τ ∈ TT, g τ := by
    intro g
    rw [← Finset.sum_filter, hTT]
  have hτ : ∀ τ, -(nτ τ * logT) + (2 * logc τ + logxi τ) ≤
      ((N - 1) / 2 + S + m * η) * (CT * N * La) + 4 * N * La * (4 * S + 4 * m * η) + N ^ 2 * La +
        (if τ ∈ TT then 2 * b' * (CT * N * La) + 24 * N * La * b' - aT τ * logT else 0) := by
    intro τ
    have r1 := hlogxi τ
    have r2 : N * (N - 1) / 2 * Real.log (2 * a) ≤ N * (N - 1) / 2 * (2 * La) :=
      mul_le_mul_of_nonneg_left hℓ (div_nonneg (mul_nonneg hN0 (by linarith)) zero_le_two)
    have r3 : 0 ≤ N * La := mul_nonneg hN0 hLa0
    have r4 := hlogc τ
    have r5 := hD1 τ
    have r6 := hD0 τ
    have r7 := hnτ τ
    have hNl : 0 ≤ (N - 1) * Real.log (2 * a) := mul_nonneg (by linarith) hℓ0
    have hNl' : (N - 1) * Real.log (2 * a) ≤ N * (2 * La) := mul_le_mul (by linarith) hℓ hℓ0 hN0
    by_cases hτT : τ ∈ TT
    · rw [if_pos hτT] at r6
      rw [if_pos hτT]
      have r8 := hlam τ hτT
      have r9 := hbT τ hτT
      have s1 : D1 τ ≤ 4 * S + 4 * m * η + 6 * b' := by linarith
      have s2 : (N - 1) * Real.log (2 * a) * D1 τ ≤
          (N - 1) * Real.log (2 * a) * (4 * S + 4 * m * η + 6 * b') := mul_le_mul_of_nonneg_left s1 hNl
      have s3 : (N - 1) * Real.log (2 * a) * (4 * S + 4 * m * η + 6 * b') ≤
          N * (2 * La) * (4 * S + 4 * m * η + 6 * b') := mul_le_mul_of_nonneg_right hNl' (by linarith)
      have u1 : (N - k) / 2 + D0 τ ≤ (N - 1) / 2 + S + m * η + 2 * b' := by linarith
      have u2 : ((N - k) / 2 + D0 τ) * logT ≤ ((N - 1) / 2 + S + m * η + 2 * b') * (CT * N * La) :=
        mul_le_mul u1 hTN hT0 (by linarith)
      rw [r7, r8]
      linarith
    · rw [if_neg hτT] at r6
      rw [if_neg hτT]
      have r8 := hlam' τ hτT
      have s1 : D1 τ ≤ 4 * S + 4 * m * η := by linarith
      have s2 : (N - 1) * Real.log (2 * a) * D1 τ ≤
          (N - 1) * Real.log (2 * a) * (4 * S + 4 * m * η) := mul_le_mul_of_nonneg_left s1 hNl
      have s3 : (N - 1) * Real.log (2 * a) * (4 * S + 4 * m * η) ≤
          N * (2 * La) * (4 * S + 4 * m * η) := mul_le_mul_of_nonneg_right hNl' (by linarith)
      have u1 : -(lam1 τ - D0 τ) ≤ (N - 1) / 2 + m * η := by linarith
      have u2 : -(lam1 τ - D0 τ) * logT ≤ ((N - 1) / 2 + m * η) * logT := mul_le_mul_of_nonneg_right u1 hT0
      have u3 : ((N - 1) / 2 + m * η) * logT ≤ ((N - 1) / 2 + S + m * η) * (CT * N * La) :=
        mul_le_mul (by linarith) hTN hT0 (by linarith)
      rw [r7]
      linarith
  have hsumτ := Finset.sum_le_sum (fun τ (_ : τ ∈ (Finset.univ : Finset Pl)) => hτ τ)
  have hLτ : ∑ τ, (-(nτ τ * logT) + (2 * logc τ + logxi τ)) =
      -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hR : ∑ τ, (((N - 1) / 2 + S + m * η) * (CT * N * La) + 4 * N * La * (4 * S + 4 * m * η) +
        N ^ 2 * La + (if τ ∈ TT then 2 * b' * (CT * N * La) + 24 * N * La * b' - aT τ * logT else 0)) =
      (Fintype.card Pl : ℝ) * (((N - 1) / 2 + S + m * η) * (CT * N * La) +
        4 * N * La * (4 * S + 4 * m * η) + N ^ 2 * La) +
        ∑ τ ∈ TT, (2 * b' * (CT * N * La) + 24 * N * La * b' - aT τ * logT) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hite]
  have hTTs : ∑ τ ∈ TT, (2 * b' * (CT * N * La) + 24 * N * La * b' - aT τ * logT) =
      (TT.card : ℝ) * (2 * b' * (CT * N * La) + 24 * N * La * b') - ∑ τ ∈ TT, aT τ * logT := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hW0 : 0 ≤ ((N - 1) / 2 + S + m * η) * (CT * N * La) + 4 * N * La * (4 * S + 4 * m * η) +
      N ^ 2 * La :=
    add_nonneg (add_nonneg (mul_nonneg (by linarith) hT0')
      (mul_nonneg (mul_nonneg (by linarith) hLa0) (by linarith))) (mul_nonneg (sq_nonneg N) hLa0)
  have hfW := mul_le_mul_of_nonneg_right hcard hW0

  have hJ : ∑ j, ((∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm) + Ch * f * N ^ 2 * (La + m ^ 3 * L)) -
        (∑ ρ, logH j ρ - Ch * f * nV ^ 2 * L')) =
      ∑ j, (∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm) + Ch * f * N ^ 2 * (La + m ^ 3 * L)) -
        ∑ j, (∑ ρ, logH j ρ - Ch * f * nV ^ 2 * L') := Finset.sum_sub_distrib _ _

  have hX1 : 0 ≤ f * N ^ 2 * La := mul_nonneg (mul_nonneg hf0 (sq_nonneg N)) hLa0
  have hX2 : 0 ≤ f * (m * η + S) * N * La := mul_nonneg (mul_nonneg (mul_nonneg hf0 (by linarith)) hN0) hLa0
  have hX3 : 0 ≤ (TT.card : ℝ) * b' * N * La :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) pb') hN0) hLa0
  have g1 : (CT / 2 + 1 + Cev) * (f * N ^ 2 * La) ≤ Ch * (f * N ^ 2 * La) :=
    mul_le_mul_of_nonneg_right (by linarith) hX1
  have g2 : (CT + 16) * (f * (m * η + S) * N * La) ≤ Ch * (f * (m * η + S) * N * La) :=
    mul_le_mul_of_nonneg_right (by linarith) hX2
  have g3 : (2 * CT + 24) * ((TT.card : ℝ) * b' * N * La) ≤ Ch * ((TT.card : ℝ) * b' * N * La) :=
    mul_le_mul_of_nonneg_right (by linarith) hX3
  have g4 : 0 ≤ CT * (f * N * La) := mul_nonneg pT (mul_nonneg (mul_nonneg hf0 hN0) hLa0)
  rw [hhu]
  linarith

end Formalism.DivisorInequality
