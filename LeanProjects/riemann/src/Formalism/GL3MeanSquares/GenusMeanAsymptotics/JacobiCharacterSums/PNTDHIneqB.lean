import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHIneqA

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem dhReBound (A P S : ℂ) (E : ℝ) (h : ‖A - P + S‖ ≤ E) : S.re ≤ P.re - A.re + E := by
  have h1 : (A - P + S).re ≤ ‖A - P + S‖ := by
    first
      | exact Complex.re_le_norm _
      | exact Complex.re_le_abs _
  simp only [Complex.add_re, Complex.sub_re] at h1
  linarith

theorem logMulAbsAddTwoLeTwoMulLog (M : ℕ) (T t : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (ht : |t| ≤ T) :
    Real.log ((M : ℝ) * (|t| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hta := abs_nonneg t
  have hpos : 0 < (M : ℝ) * (|t| + 2) := by positivity
  have h1 : (M : ℝ) * (|t| + 2) ≤ (M : ℝ) * (T + 2) := by nlinarith
  have h2 : (M : ℝ) * (T + 2) ≤ ((M : ℝ) * T) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ) - 3) (by linarith : (0 : ℝ) ≤ T - 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ)) (by linarith : (0 : ℝ) ≤ T - 2)]
  calc Real.log ((M : ℝ) * (|t| + 2)) ≤ Real.log (((M : ℝ) * T) ^ 2) :=
        Real.log_le_log hpos (h1.trans h2)
    _ = 2 * Real.log ((M : ℝ) * T) := by rw [Real.log_pow]; norm_num

theorem dhLogOne (M : ℕ) (T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (6 : ℝ) ≤ M * T := by nlinarith
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ≤ (M : ℝ) * T := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) h1

theorem dhPair (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : β₁ < 1) (k : ℕ) (s : ℂ)
    (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) :
    (1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)).re ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
  have hδ : 0 < 1 - β₁ := by linarith
  have hare : (s - 1).re = η := by rw [hs]; simp
  have hbre : (s - β₁).re = η + (1 - β₁) := by rw [hs]; simp; ring
  have hna : η ≤ ‖s - 1‖ := hare ▸ Complex.re_le_norm (s - 1)
  have hnb : η ≤ ‖s - β₁‖ := le_trans (by linarith) (hbre ▸ Complex.re_le_norm (s - β₁))
  have ha0 : s - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hna; linarith
  have hb0 : s - β₁ ≠ 0 := fun h => by rw [h, norm_zero] at hnb; linarith
  have hba : (s - β₁) - (s - 1) = ((1 - β₁ : ℝ) : ℂ) := by push_cast; ring
  have hid : 1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1) =
      ((s - β₁) - (s - 1)) * (∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)) /
        ((s - 1) ^ (k + 1) * (s - β₁) ^ (k + 1)) := by
    rw [mul_comm ((s - β₁) - (s - 1)), geom_sum₂_mul]
    field_simp
  have hsum : ‖∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ ≤
      ((k + 1 : ℕ) : ℝ) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2)) := by
    calc _ ≤ ∑ i ∈ Finset.range (k + 1), ‖(s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (k + 1), ‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [norm_mul, norm_pow, norm_pow, le_div_iff₀ (by positivity)]
          have e1 : η ^ (k + 2) = η ^ (i + 1) * η ^ (k + 1 - i) := by rw [← pow_add]; congr 1; omega
          have e2 : ‖s - 1‖ ^ (k + 1) = ‖s - 1‖ ^ (k + 1 - 1 - i) * ‖s - 1‖ ^ (i + 1) := by
            rw [← pow_add]; congr 1; omega
          have e3 : ‖s - β₁‖ ^ (k + 1) = ‖s - β₁‖ ^ i * ‖s - β₁‖ ^ (k + 1 - i) := by
            rw [← pow_add]; congr 1; omega
          rw [e1, e2, e3]
          have p1 : η ^ (i + 1) ≤ ‖s - 1‖ ^ (i + 1) := pow_le_pow_left₀ hη.le hna _
          have p2 : η ^ (k + 1 - i) ≤ ‖s - β₁‖ ^ (k + 1 - i) := pow_le_pow_left₀ hη.le hnb _
          have p12 := mul_le_mul p1 p2 (by positivity) (by positivity)
          calc ‖s - β₁‖ ^ i * ‖s - 1‖ ^ (k + 1 - 1 - i) * (η ^ (i + 1) * η ^ (k + 1 - i))
              ≤ ‖s - β₁‖ ^ i * ‖s - 1‖ ^ (k + 1 - 1 - i) * (‖s - 1‖ ^ (i + 1) * ‖s - β₁‖ ^ (k + 1 - i)) :=
                mul_le_mul_of_nonneg_left p12 (by positivity)
            _ = _ := by ring
      _ = ((k + 1 : ℕ) : ℝ) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfinal : ‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
    rw [hid, norm_div, norm_mul, hba, Complex.norm_real, Real.norm_of_nonneg hδ.le, norm_mul, norm_pow, norm_pow]
    have hpos : 0 < ‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) := by
      have := norm_pos_iff.mpr ha0
      have := norm_pos_iff.mpr hb0
      positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have h3 := mul_le_mul_of_nonneg_left hsum hδ.le
    push_cast at h3
    calc (1 - β₁) * ‖∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ * η ^ (k + 2)
        ≤ (1 - β₁) * (((k : ℝ) + 1) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2))) * η ^ (k + 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ((k : ℝ) + 1) * (1 - β₁) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1)) := by
          field_simp
  have hre : (1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)).re ≤
      ‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ := Complex.re_le_norm _
  exact hre.trans hfinal

theorem dhAssemble {β : Type*} [AddCommGroup β] (F1 F2 F3 F4 : Multiset ℂ) (b2 b3 b4 : ℂ)
    (c3 c4 : Prop) [Decidable c3] [Decidable c4] (h2 : b2 ∈ F2) (h3 : c3 → b3 ∈ F3) (h4 : c4 → b4 ∈ F4)
    (g : ℂ → β) :
    ((F1 + F2.erase b2 + (if c3 then F3.erase b3 else F3) + (if c4 then F4.erase b4 else F4)).map g).sum
      = (F1.map g).sum + (F2.map g).sum + (F3.map g).sum + (F4.map g).sum - g b2
        - (if c3 then g b3 else 0) - (if c4 then g b4 else 0) := by
  classical
  have e : ∀ (F : Multiset ℂ) (b : ℂ), b ∈ F → ((F.erase b).map g).sum = (F.map g).sum - g b := by
    intro F b hb
    rw [← Multiset.sum_map_erase hb]
    abel
  simp only [Multiset.map_add, Multiset.sum_add, e _ _ h2]
  by_cases hc3 : c3 <;> by_cases hc4 : c4
  · simp only [if_pos hc3, if_pos hc4, e _ _ (h3 hc3), e _ _ (h4 hc4)]
    abel
  · simp only [if_pos hc3, if_neg hc4, e _ _ (h3 hc3)]
    abel
  · simp only [if_neg hc3, if_pos hc4, e _ _ (h4 hc4)]
    abel
  · simp only [if_neg hc3, if_neg hc4]
    abel

theorem dhFam_re (Z : Finset ℂ) (m : ℂ → ℕ) (s x : ℂ) (η : ℝ) (hZ : ∀ ρ ∈ Z, ρ.re < 1)
    (hs : s.re = 1 + η) (hx : x ∈ dhFam Z m s) : η ≤ x.re := by
  unfold dhFam at hx
  rw [Multiset.mem_bind] at hx
  obtain ⟨ρ, hρ, hx⟩ := hx
  rw [Multiset.eq_of_mem_replicate hx, Complex.sub_re, hs]
  linarith [hZ ρ hρ]

theorem dhMemIte (F : Multiset ℂ) (c : Prop) [Decidable c] (b x : ℂ) (h : x ∈ (if c then F.erase b else F)) :
    x ∈ F := by
  split_ifs at h
  · exact Multiset.mem_of_mem_erase h
  · exact h

theorem dhFamPow (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (k : ℕ) :
    ((dhFam Z m s).map (fun x => 1 / x ^ (k + 1))).sum = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
  unfold dhFam
  rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun ρ _ => ?_
  simp [Multiset.map_replicate, Multiset.sum_replicate, div_eq_mul_inv]

theorem dhFinalArith (S1 S2 S3 S4 P1 P3 P4 A1 A2 A3 A4 E0 Eγ g2 I3 I4 X F G Hc H e8 : ℝ)
    (t1 : S1 + S2 + S3 + S4 ≤ P1 - A1 + E0 + (0 - A2 + E0) + (P3 - A3 + Eγ) + (P4 - A4 + Eγ))
    (hA : 0 ≤ A1 + A2 + A3 + A4) (hp : P1 - g2 ≤ X) (hs : P3 + P4 - I3 - I4 ≤ X + e8)
    (h0 : E0 ≤ F) (hγ : Eγ ≤ F) (t3 : F ≤ 2 * G) (t2 : e8 ≤ H) (nn : 0 ≤ Hc) :
    S1 + S2 + S3 + S4 - g2 - I3 - I4 ≤ 2 * X + (8 * G + 8 * Hc + H) := by
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
