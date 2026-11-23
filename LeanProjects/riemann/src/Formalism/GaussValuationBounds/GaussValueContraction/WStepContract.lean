import Formalism.GaussValuationBounds.Statement

namespace Formalism.NOK

theorem wStep_mono {ℓ H H' lam a a' : ℝ} (hℓ : 3 ≤ ℓ) (hH : H ≤ H') (ha : a ≤ a') :
    WStep ℓ H lam a ≤ WStep ℓ H' lam a' := by
  have hd : 0 < ℓ - 1 := by linarith
  have hD : 0 < ℓ ^ 2 - ℓ + 1 := by nlinarith
  unfold WStep
  have h1 : H / (ℓ - 1) ≤ H' / (ℓ - 1) := div_le_div_of_nonneg_right hH hd.le
  have h2 : (ℓ * a + (ℓ - 1) * (H + lam)) / (ℓ ^ 2 - ℓ + 1) ≤
      (ℓ * a' + (ℓ - 1) * (H' + lam)) / (ℓ ^ 2 - ℓ + 1) := by
    apply div_le_div_of_nonneg_right _ hD.le
    have : ℓ * a ≤ ℓ * a' := mul_le_mul_of_nonneg_left ha (by linarith)
    have : (ℓ - 1) * (H + lam) ≤ (ℓ - 1) * (H' + lam) :=
      mul_le_mul_of_nonneg_left (by linarith) hd.le
    linarith
  have := max_le_max h1 h2
  linarith

theorem wStep_contract {ℓ H lam z t : ℝ} (hℓ : 3 ≤ ℓ) (hlam : 0 ≤ lam) (hz : 0 ≤ z)
    (hH : H + lam = (ℓ - 1) * t) :
    WStep ℓ H lam ((ℓ - 1) * z + t + 2) ≤ z + t + 2 := by
  have hd : 0 < ℓ - 1 := by linarith
  have hD : 0 < ℓ ^ 2 - ℓ + 1 := by nlinarith
  have e1 : H / (ℓ - 1) ≤ z + t + 1 := by
    rw [div_le_iff₀ hd]; nlinarith
  have e2 : (ℓ * ((ℓ - 1) * z + t + 2) + (ℓ - 1) * (H + lam)) / (ℓ ^ 2 - ℓ + 1) ≤ z + t + 1 := by
    rw [div_le_iff₀ hD, hH]; nlinarith
  unfold WStep
  have := max_le e1 e2
  linarith

theorem wCycle_proof : WCycle := by
  intro n _ ℓ lam Hm a H hℓ hlam hH hstep i
  have hd : 0 < ℓ - 1 := by linarith
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  have hm : ∀ i, a i ≤ a i₀ := fun i => hi₀ i (Finset.mem_univ i)
  have h1 := hstep (i₀ + 1)
  rw [add_sub_cancel_right] at h1
  have h2 : a i₀ ≤ WStep ℓ Hm lam (a i₀) := le_trans h1 (wStep_mono hℓ (hH _) (hm _))
  have key : a i₀ ≤ (Hm + lam) / (ℓ - 1) + 2 := by
    unfold WStep at h2
    have h3 : a i₀ - 1 ≤ max (Hm / (ℓ - 1)) ((ℓ * a i₀ + (ℓ - 1) * (Hm + lam)) / (ℓ ^ 2 - ℓ + 1)) := by
      linarith
    rcases le_max_iff.mp h3 with h4 | h4
    · have : Hm / (ℓ - 1) ≤ (Hm + lam) / (ℓ - 1) := div_le_div_of_nonneg_right (by linarith) hd.le
      linarith
    · have hD : 0 < ℓ ^ 2 - ℓ + 1 := by nlinarith
      rw [le_div_iff₀ hD] at h4
      have h5 : a i₀ * (ℓ - 1) ≤ Hm + lam + 2 * (ℓ - 1) := by
        by_contra hc
        rw [not_le] at hc
        have := mul_lt_mul_of_pos_left hc hd
        nlinarith
      have : a i₀ ≤ (Hm + lam + 2 * (ℓ - 1)) / (ℓ - 1) := by rw [le_div_iff₀ hd]; exact h5
      have e : (Hm + lam + 2 * (ℓ - 1)) / (ℓ - 1) = (Hm + lam) / (ℓ - 1) + 2 := by
        field_simp
      linarith
  exact le_trans (hm i) key

theorem wThin_proof : WThin := by
  intro ℓ lam G X₀ j x H hℓ hlam hG hX₀ hx0 hH hstep
  have hd : 0 < ℓ - 1 := by linarith
  set t := (2 * G + lam) / (ℓ - 1) with ht
  have htH : 2 * G + lam = (ℓ - 1) * t := by rw [ht]; field_simp
  have claim : ∀ k, k ≤ j → x k ≤ X₀ / (ℓ - 1) ^ k + t + 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      have : 0 ≤ t := div_nonneg (by linarith) hd.le
      simp only [pow_zero, div_one]
      linarith
    | succ k ih =>
      intro hk
      have hk' : k < j := by omega
      have hprev := ih hk'.le
      set z := X₀ / (ℓ - 1) ^ (k + 1) with hzdef
      have hz : 0 ≤ z := div_nonneg hX₀ (pow_nonneg hd.le _)
      have hzk : X₀ / (ℓ - 1) ^ k = (ℓ - 1) * z := by
        rw [hzdef, pow_succ]; field_simp
      rw [hzk] at hprev
      calc x (k + 1) ≤ WStep ℓ (H k) lam (x k) := hstep k hk'
        _ ≤ WStep ℓ (2 * G) lam ((ℓ - 1) * z + t + 2) := wStep_mono hℓ (hH k hk') hprev
        _ ≤ z + t + 2 := wStep_contract hℓ hlam hz htH
  have := claim j le_rfl
  linarith

theorem wCut_proof : WCut := by
  intro n _ ℓ lam h G a H c j hℓ hlam hh hG hH hthin hstep
  have hd : 0 < ℓ - 1 := by linarith
  set X₀ := (2 * h + lam) / (ℓ - 1) + 2 with hX₀def
  have hX₀ : 0 ≤ X₀ := by
    have : 0 ≤ (2 * h + lam) / (ℓ - 1) := div_nonneg (by linarith) hd.le
    linarith
  have hA : ∀ i, a i ≤ X₀ := wCycle_proof n ℓ lam (2 * h) a H hℓ hlam hH hstep
  have := wThin_proof ℓ lam G X₀ j (fun k => a (c + ((j - k : ℕ) : ZMod n)))
    (fun k => H (c + ((j - k : ℕ) : ZMod n))) hℓ hlam hG hX₀ (hA _)
    (fun k hk => hthin (j - k) (by omega) (by omega))
    (by
      intro k hk
      have e1 : ((j - k : ℕ) : ZMod n) = ((j - (k + 1) : ℕ) : ZMod n) + 1 := by
        rw [show j - k = (j - (k + 1)) + 1 by omega]
        push_cast
        ring
      have e2 : c + ((j - k : ℕ) : ZMod n) - 1 = c + ((j - (k + 1) : ℕ) : ZMod n) := by
        rw [e1]; ring
      have h1 := hstep (c + ((j - k : ℕ) : ZMod n))
      rw [e2] at h1
      exact h1)
  simpa using this

end Formalism.NOK
