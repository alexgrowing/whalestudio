import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NkExponent
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeBeyond

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem nk_toNat_cast (z : ℤ) (h : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = ((z : ℤ) : ℝ) := by
  have e := Int.toNat_of_nonneg h
  exact_mod_cast congrArg (Int.cast : ℤ → ℝ) e

theorem brk_hat (m : ℕ) (η δ a : ℝ) (hη0 : 0 ≤ η) (hδη : δ ≤ η) (hδ0 : 0 ≤ δ) (hA0 : 0 ≤ a)
    (hm : (m : ℝ) ≤ η * a) : (a + m) * (1 + δ) ≤ Real.exp (2 * η) * a := by
  have h1 : 1 + η ≤ Real.exp η := by linarith [Real.add_one_le_exp η]
  have h2 : (1 + η) ^ 2 ≤ Real.exp (2 * η) := by
    rw [show 2 * η = η + η by ring, Real.exp_add, ← sq]
    exact pow_le_pow_left₀ (by linarith) h1 2
  calc (a + m) * (1 + δ) ≤ (a + η * a) * (1 + η) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by nlinarith)
    _ = a * (1 + η) ^ 2 := by ring
    _ ≤ a * Real.exp (2 * η) := mul_le_mul_of_nonneg_left h2 hA0
    _ = Real.exp (2 * η) * a := by ring

set_option maxHeartbeats 400000 in

theorem brk_core (s m : ℕ) (La p A lam0 : ℝ) (Ai Ci ρ u nn : Fin s → ℝ) (cc : ℕ → ℝ)
    (hroom : 2 * s + 1 ≤ m) (hk10 : 10 ≤ (m : ℝ) + 1) (hLa1 : 1 ≤ La) (hLak : 4 * La ≤ (m : ℝ) + 1)
    (hpk : ((m : ℝ) + 1) ^ 2 ≤ p) (hkA : ((m : ℝ) + 1) ^ 3 ≤ A) (hkAi : ∀ i, ((m : ℝ) + 1) ^ 3 ≤ Ai i)
    (hkCi : ∀ i, ((m : ℝ) + 1) ^ 3 ≤ Ci i) (hC0 : cc 0 = A) (hCnn : ∀ l, 0 ≤ cc l)
    (hρ : ∀ i, 0 ≤ ρ i ∧ ρ i ≤ cc i ∧ ρ i ≤ Ai i * (1 + 4 / p ^ 2) ∧ -(4 * Ai i / p ^ 2) ≤ u i)
    (hrec : ∀ i : Fin s, cc (i + 1) = cc i + Ai i - u i - ρ i)
    (hl0 : 0 ≤ lam0) (hls : lam0 ≤ cc s) (hn : ∀ i, 0 ≤ nn i ∧ nn i ≤ Ci i * (1 + 4 / p ^ 2))
    (hk : ∃ i0, ¬ (u i0 + 4 * (Ai i0 + m) / p ^ 2 ≤ La * max (cc i0) (Ai i0) / ((m : ℝ) + 1) ∧
      Ci i0 * (1 - La / ((m : ℝ) + 1)) ≤ nn i0)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ^ (m - 1) ≤ Real.exp (2 - La / 5) ∧
      (lam0 + m) * (∏ i, (ρ i + m)) * (∏ i, (nn i + m)) ≤ θ * (A * (∏ i, Ai i) * ∏ i, Ci i) := by
  set k : ℝ := (m : ℝ) + 1 with hkdef
  have hk0 : 0 < k := by linarith
  set η : ℝ := 1 / k ^ 2 with hη
  set τ : ℝ := La / (4 * k) with hτ
  set δ : ℝ := 4 / p ^ 2 with hδ
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 100 := by
    rw [hη, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hp0 : (0 : ℝ) < p := by nlinarith
  have hδη : δ ≤ η := by
    rw [hδ, hη, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : k ^ 4 ≤ p ^ 2 := by
      have : k ^ 4 = (k ^ 2) ^ 2 := by ring
      rw [this]; exact pow_le_pow_left₀ (by positivity) hpk 2
    have hk2 : (4 : ℝ) ≤ k ^ 2 := by nlinarith
    have h6 := mul_le_mul_of_nonneg_left hk2 (sq_nonneg k)
    have h7 : k ^ 4 = k ^ 2 * k ^ 2 := by ring
    linarith
  have hδ0 : 0 ≤ δ := by positivity
  have hmη : ∀ y : ℝ, k ^ 3 ≤ y → (m : ℝ) ≤ η * y := by
    intro y hy
    rw [hη, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have : (m : ℝ) ≤ k := by linarith
    nlinarith
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 / 4 := by
    rw [hτ, div_lt_iff₀ (by positivity)]
    nlinarith
  have hE2one : 1 ≤ Real.exp (2 * η) := by linarith [Real.add_one_le_exp (2 * η)]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  let c : ℕ → ℝ := fun l => cc l + m
  have hc0 : ∀ l, 0 ≤ c l := fun l => by have := hCnn l; show 0 ≤ cc l + m; linarith
  have hAi0 : ∀ i, 0 ≤ Ai i := fun i => le_trans (by positivity) (hkAi i)
  have hCi0 : ∀ i, 0 ≤ Ci i := fun i => le_trans (by positivity) (hkCi i)
  have hAhat : ∀ i, (Ai i + m) * (1 + δ) ≤ Real.exp (2 * η) * Ai i := fun i =>
    brk_hat m η δ (Ai i) hη0.le hδη hδ0 (hAi0 i) (hmη _ (hkAi i))
  have hstep0 : ∀ (i : Fin s) (κ : ℝ),
      (ρ i + m) * (c i + ((Ai i + m) * (1 + δ)) - (u i + δ * (Ai i + m)) - (ρ i + m)) ≤
        κ * (c i * ((Ai i + m) * (1 + δ))) → 0 ≤ κ →
      (ρ i + m) * c (i + 1) ≤ (κ * (Real.exp (2 * η) * Ai i)) * c i := by
    intro i κ h hκ
    have hcs : c (i + 1) = c i + ((Ai i + m) * (1 + δ)) - (u i + δ * (Ai i + m)) - (ρ i + m) := by
      show cc (i + 1) + m = _
      rw [hrec i]
      show _ = cc i + m + _ - _ - _
      ring
    rw [hcs]
    refine h.trans ?_
    exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hAhat i) (hc0 i)) hκ) (le_of_eq (by ring))
  have hfacts : ∀ i : Fin s, 0 ≤ ρ i + m ∧ ρ i + m ≤ c i ∧ ρ i + m ≤ (Ai i + m) * (1 + δ) ∧
      0 ≤ u i + δ * (Ai i + m) := fun i => by
    obtain ⟨hr0, hrc, hrA, hu⟩ := hρ i
    have hA0 := hAi0 i
    refine ⟨by linarith, by show _ ≤ cc i + m; linarith, ?_, ?_⟩
    · have : ρ i ≤ Ai i * (1 + δ) := by rw [hδ]; exact hrA
      nlinarith
    · have : -(δ * Ai i) ≤ u i := by
        have e : -(4 * Ai i / p ^ 2) = -(δ * Ai i) := by rw [hδ]; ring
        rw [← e]; exact hu
      nlinarith
  have hr9 : 9 ≤ m := by
    have : (9 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast this
  have hcA : c 0 ≤ Real.exp η * A := by
    show cc 0 + m ≤ _
    rw [hC0]
    have := hmη _ hkA
    have hA0 : 0 ≤ A := le_trans (by positivity) hkA
    nlinarith [Real.add_one_le_exp η]
  have hl : lam0 + m ≤ c s := by show _ ≤ cc s + m; linarith
  have hnn1 : ∀ i : Fin s, nn i + m ≤ 1 * (Real.exp (2 * η) * Ci i) := fun i => by
    obtain ⟨h0, h1⟩ := hn i
    have hm := hmη _ (hkCi i)
    have hC0' := hCi0 i
    have : nn i ≤ Ci i * (1 + δ) := by rw [hδ]; exact h1
    have hE : 1 + 2 * η ≤ Real.exp (2 * η) := by linarith [Real.add_one_le_exp (2 * η)]
    nlinarith
  have fin : ∀ κ μ : Fin s → ℝ, (∀ i, 0 ≤ κ i) → (∀ i, 0 ≤ μ i) →
      (∀ i : Fin s, (ρ i + m) * c (i + 1) ≤ (κ i * (Real.exp (2 * η) * Ai i)) * c i) →
      (∀ i : Fin s, nn i + m ≤ μ i * (Real.exp (2 * η) * Ci i)) →
      (∏ i, κ i) * (∏ i, μ i) ≤ Real.exp (-τ) →
      ∃ θ : ℝ, 0 ≤ θ ∧ θ ^ (m - 1) ≤ Real.exp (2 - La / 5) ∧
        (lam0 + m) * (∏ i, (ρ i + m)) * (∏ i, (nn i + m)) ≤ θ * (A * (∏ i, Ai i) * ∏ i, Ci i) := by
    intro κ μ hκ hμ hst hnn hγ
    have hγ0 : 0 ≤ (∏ i, κ i) * (∏ i, μ i) :=
      mul_nonneg (Finset.prod_nonneg fun i _ => hκ i) (Finset.prod_nonneg fun i _ => hμ i)
    refine ⟨Real.exp η * Real.exp (2 * η) ^ s * Real.exp (2 * η) ^ s * ((∏ i, κ i) * (∏ i, μ i)), by positivity, ?_, ?_⟩
    · have hEq1 : Real.exp η = Real.exp (1 / ((m : ℝ) + 1) ^ 2) := by rw [hη]
      have hEq2 : Real.exp (2 * η) = Real.exp (2 / ((m : ℝ) + 1) ^ 2) := by
        rw [hη]
        congr 1
        rw [hkdef]
        ring
      have hτeq : τ = La / (4 * ((m : ℝ) + 1)) := by rw [hτ]
      rw [hEq1, hEq2]
      exact nk_exponent s m La _ hr9 hroom (by linarith) hγ0 (by rw [← hτeq]; exact hγ)
    · exact nk_bracket s c (fun i => ρ i + m) (fun i => nn i + m) Ai Ci κ μ (lam0 + m) A (Real.exp η)
        (Real.exp (2 * η)) hc0 (fun i => (hfacts i).1) (fun i => by have := (hn i).1; linarith) hAi0 hCi0 hκ hμ
        (by linarith) (by positivity) hst hl hnn hcA
  obtain ⟨i0, hi0⟩ := hk
  by_cases hP : u i0 + 4 * (Ai i0 + m) / p ^ 2 ≤ La * max (cc i0) (Ai i0) / ((m : ℝ) + 1)
  · have hQ : ¬ (Ci i0 * (1 - La / ((m : ℝ) + 1)) ≤ nn i0) := fun h => hi0 ⟨hP, h⟩
    push Not at hQ
    set μ0 : ℝ := 1 - La / k + η with hμ0
    have hμ00 : 0 ≤ μ0 := by
      have : La / k ≤ 1 / 4 := by rw [div_le_iff₀ hk0]; linarith
      linarith
    refine fin (fun _ => 1) (fun i => if i = i0 then μ0 else 1) (fun _ => zero_le_one)
      (fun i => by split_ifs <;> linarith) (fun i => ?_) (fun i => ?_) ?_
    · obtain ⟨hr0, hrc, hrA, hu⟩ := hfacts i
      refine hstep0 i 1 ?_ zero_le_one
      rw [one_mul]
      exact nk_iv _ _ _ _ hr0 hrc hrA hu
    · by_cases hi : i = i0
      · subst hi
        rw [if_pos rfl]
        have hm := hmη _ (hkCi i)
        have hC0' := hCi0 i
        have h1 : nn i + m ≤ μ0 * Ci i := by rw [hμ0]; nlinarith
        calc _ ≤ μ0 * Ci i := h1
          _ ≤ μ0 * (Real.exp (2 * η) * Ci i) := mul_le_mul_of_nonneg_left (by nlinarith) hμ00
      · rw [if_neg hi]; exact hnn1 i
    · rw [Finset.prod_const_one, one_mul, Finset.prod_ite_eq' Finset.univ i0 (fun _ => μ0), if_pos (Finset.mem_univ _)]
      refine le_trans (show μ0 ≤ Real.exp (-(La / k) + η) by linarith [Real.add_one_le_exp (-(La / k) + η)])
        (Real.exp_le_exp.mpr ?_)
      rw [hτ]
      have h1 : η ≤ 3 * La / (4 * k) := by
        rw [hη, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have h2 : La / (4 * k) = La / k - 3 * La / (4 * k) := by field_simp; ring
      linarith
  · push Not at hP
    refine fin (fun i => if i = i0 then 1 - τ else 1) (fun _ => 1) (fun i => by split_ifs <;> linarith)
      (fun _ => zero_le_one) (fun i => ?_) hnn1 ?_
    · obtain ⟨hr0, hrc, hrA, hu⟩ := hfacts i
      by_cases hi : i = i0
      · subst hi
        rw [if_pos rfl]
        refine hstep0 i (1 - τ) ?_ (by linarith)
        have hcpos : 0 < c i := by
          have := hCnn i
          show 0 < cc i + m
          linarith
        have hA0 := hAi0 i
        have hApos : 0 < (Ai i + m) * (1 + δ) := by positivity
        apply nk_vi _ _ _ _ _ hcpos hApos hr0 hrc hrA hu hτ0 hτ1
        have hmax : max (c i) ((Ai i + m) * (1 + δ)) ≤ 2 * max (cc i) (Ai i) := by
          have hm := hmη _ (hkAi i)
          have hAh := hAhat i
          have hcm : cc i ≤ max (cc i) (Ai i) := le_max_left _ _
          have hAm : Ai i ≤ max (cc i) (Ai i) := le_max_right _ _
          apply max_le
          · show cc i + m ≤ _
            have : (m : ℝ) ≤ Ai i := by nlinarith
            linarith
          · have : Real.exp (2 * η) * Ai i ≤ 2 * Ai i := by
              have : Real.exp (2 * η) ≤ 2 := by
                have h2η : 2 * η ≤ 1 / 50 := by linarith
                have := Real.exp_le_exp.mpr h2η
                have h3 : Real.exp (1 / 50) ≤ 2 := by
                  have := Real.log_two_gt_d9
                  calc Real.exp (1 / 50) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
                    _ = 2 := Real.exp_log (by norm_num)
                linarith
              nlinarith
            linarith
        have e : 2 * τ * (2 * max (cc i) (Ai i)) = La * max (cc i) (Ai i) / ((m : ℝ) + 1) := by
          rw [hτ]; field_simp; ring
        have e2 : 4 * (Ai i + m) / p ^ 2 = δ * (Ai i + m) := by rw [hδ]; ring
        have := mul_le_mul_of_nonneg_left hmax (by linarith : (0:ℝ) ≤ 2 * τ)
        rw [e2] at hP
        linarith
      · rw [if_neg hi]
        refine hstep0 i 1 ?_ zero_le_one
        rw [one_mul]
        exact nk_iv _ _ _ _ hr0 hrc hrA hu
    · rw [Finset.prod_const_one, mul_one, Finset.prod_ite_eq' Finset.univ i0 (fun _ => 1 - τ),
        if_pos (Finset.mem_univ _)]
      linarith [Real.add_one_le_exp (-τ)]

theorem bracket_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hF : PairFactsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hN : CoarseDegreesLargeAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : BracketAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hp hk
  obtain ⟨hC0, hCnn, hρ, hl0, hls, hn⟩ := hF X hD hI hc j rz ry hd A hA1 hA2 mu lam hp
  obtain ⟨hkA, hkAi, hkCi, hpk, hk10, hLa1, hLak⟩ := hN X hD hI hc j rz ry hd A hA1
  have hroom : 2 * segS X.TT j + 1 ≤ X.m := by
    obtain ⟨⟨-, -, -, -, h5, -, h7, -⟩, -⟩ := hI
    have := (h5 j).2
    omega
  have hkdef : X.k = (X.m : ℝ) + 1 := rfl
  rw [hkdef] at hkA hkAi hkCi hpk hk10 hLak
  have hk' : ∃ i0, ¬ ((((pairO mu (clA C0 CE1 CE2 X j rz ry) i0 - pairRho mu i0 : ℤ) : ℝ)) +
      4 * ((clA C0 CE1 CE2 X j rz ry i0 : ℝ) + X.m) / (X.p : ℝ) ^ 2 ≤
        X.La C0 * max ((pairC mu i0 : ℤ) : ℝ) (clA C0 CE1 CE2 X j rz ry i0 : ℝ) / ((X.m : ℝ) + 1) ∧
      (clC C0 CE1 CE2 X j rz ry i0 : ℝ) * (1 - X.La C0 / ((X.m : ℝ) + 1)) ≤
        ((pairN (s := segS X.TT j) lam i0 : ℤ) : ℝ)) := by
    unfold KeptPair at hk
    exact not_forall.mp hk
  obtain ⟨θ, h0, h1, h2⟩ := brk_core (segS X.TT j) X.m (X.La C0) (X.p : ℝ) (A : ℝ) ((lam 0 : ℤ) : ℝ)
    (fun i => (clA C0 CE1 CE2 X j rz ry i : ℝ)) (fun i => (clC C0 CE1 CE2 X j rz ry i : ℝ))
    (fun i => ((pairRho mu i : ℤ) : ℝ)) (fun i => ((pairO mu (clA C0 CE1 CE2 X j rz ry) i - pairRho mu i : ℤ) : ℝ))
    (fun i => ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ)) (fun l => ((pairC mu l : ℤ) : ℝ))
    hroom hk10 hLa1 hLak hpk hkA hkAi hkCi (by simp only [hC0]; push_cast; rfl)
    (fun l => by have := hCnn l; exact_mod_cast this)
    (fun i => by
      obtain ⟨a, b, c, d⟩ := hρ i
      exact ⟨by exact_mod_cast a, by exact_mod_cast b, c, d⟩)
    (fun i => by simp only [pairO]; push_cast; ring)
    (by exact_mod_cast hl0) (by exact_mod_cast hls)
    (fun i => by
      obtain ⟨a, b⟩ := hn i
      exact ⟨by exact_mod_cast a, b⟩) hk'
  refine ⟨θ, h0, h1, ?_⟩
  have e0 : (((lam 0).toNat : ℝ) + X.m) = ((lam 0 : ℤ) : ℝ) + X.m := by rw [nk_toNat_cast _ hl0]
  have e1 : ∏ i : Fin (segS X.TT j), (((pairRho mu i).toNat : ℝ) + X.m) =
      ∏ i : Fin (segS X.TT j), (((pairRho mu i : ℤ) : ℝ) + X.m) :=
    Finset.prod_congr rfl fun i _ => by rw [nk_toNat_cast _ (hρ i).1]
  have e2 : ∏ i : Fin (segS X.TT j), (((pairN (s := segS X.TT j) lam i).toNat : ℝ) + X.m) =
      ∏ i : Fin (segS X.TT j), (((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) + X.m) :=
    Finset.prod_congr rfl fun i _ => by rw [nk_toNat_cast _ (hn i).1]
  rw [e0, e1, e2]
  exact h2

theorem restBracket_of (hF : RestPairFacts) (hN : CoarseDegreesLargeBeyond) : RestBracket :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => bracket_of h.1 h.2) (hF.and hN)

end Formalism.MainNotions.ColumnSystems.Pf
