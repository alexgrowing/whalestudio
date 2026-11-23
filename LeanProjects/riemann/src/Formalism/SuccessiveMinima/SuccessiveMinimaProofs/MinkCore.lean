import Formalism.SuccessiveMinima.DefsMink

open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

theorem partialBoxVolumeTopLeOne : GjTop := by
  intro n A
  unfold Gj
  calc volume (boxJ n n ∩ (A + latJ n n)) ≤ volume (boxJ n n) :=
        measure_mono Set.inter_subset_left
    _ ≤ volume (Set.univ.pi fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
        apply measure_mono
        intro u hu i _
        exact hu i i.2
    _ = 1 := by
        rw [Real.volume_pi_Ico]
        simp

theorem gjZero (n : ℕ) (A : Set (Fin n → ℝ)) : Gj n 0 A = volume A := by
  unfold Gj
  have h1 : boxJ n 0 = Set.univ := by
    ext u
    simp [boxJ]
  have h2 : latJ n 0 = {0} := by
    ext k
    simp only [latJ, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, hk⟩
      funext i
      exact hk i (Nat.zero_le _)
    · rintro rfl
      exact ⟨fun _ => ⟨0, by simp⟩, fun _ _ => rfl⟩
  rw [h1, h2, Set.univ_inter]
  simp

theorem minkCore_of (h3 : GjLevel) (h4 : GjScale) : MinkCore := by
  intro n C lam hCo hCc hCs hCb hpos hmono hsep
  have hsmulC : ∀ k : Fin n, IsOpen (lam k • C) := fun k => hCo.smul₀ (hpos k).ne'
  have hlev : ∀ k : Fin n, Gj n k (lam k • C) ≤ Gj n (k + 1) (lam k • C) := by
    intro k
    apply h3 n k (lam k • C) k.2 (hsmulC k)
    intro x hx y hy hxy i hi
    exact hsep k x hx y hy hxy i (Fin.le_def.mpr hi)
  have hbase : ∀ hk : 0 < n, ENNReal.ofReal (∏ i, min (lam i) (lam ⟨0, hk⟩)) * volume C
      ≤ Gj n 0 (lam ⟨0, hk⟩ • C) := by
    intro hk
    rw [gjZero, Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos (hpos _) n)]
    have e : ∏ i, min (lam i) (lam ⟨0, hk⟩) = lam ⟨0, hk⟩ ^ n := by
      rw [Finset.prod_congr rfl
        (fun i _ => min_eq_right (hmono (show (⟨0, hk⟩ : Fin n) ≤ i from
          Fin.le_def.mpr (Nat.zero_le (i : ℕ)))))]
      simp
    rw [e]
  have hstep : ∀ k (hk0 : k < n) (hk : k + 1 < n),
      ∏ i, min (lam i) (lam ⟨k + 1, hk⟩) =
        (lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1)) * ∏ i, min (lam i) (lam ⟨k, hk0⟩) := by
    intro k hk0 hk
    have hab : lam ⟨k, hk0⟩ ≤ lam ⟨k + 1, hk⟩ := hmono (Fin.mk_le_mk.mpr (by omega))
    have ha0 : 0 < lam ⟨k, hk0⟩ := hpos _
    have hfac : ∀ i : Fin n, min (lam i) (lam ⟨k + 1, hk⟩) =
        (if k < (i : ℕ) then lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩ else 1) * min (lam i) (lam ⟨k, hk0⟩) := by
      intro i
      split_ifs with h
      · have h1 : lam ⟨k + 1, hk⟩ ≤ lam i := hmono (Fin.le_def.mpr (show k + 1 ≤ (i : ℕ) by omega))
        rw [min_eq_right h1, min_eq_right (hab.trans h1), div_mul_cancel₀ _ ha0.ne']
      · have h1 : lam i ≤ lam ⟨k, hk0⟩ := hmono (Fin.le_def.mpr (show (i : ℕ) ≤ k by omega))
        rw [min_eq_left (h1.trans hab), min_eq_left h1, one_mul]
    have hcard : (Finset.univ.filter fun i : Fin n => k < (i : ℕ)).card = n - (k + 1) := by
      have e : (Finset.univ.filter fun i : Fin n => k < (i : ℕ)) = Finset.Ioi ⟨k, hk0⟩ := by
        ext i
        simp [Fin.lt_def]
      rw [e, Fin.card_Ioi]
      simp only
      omega
    rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const_one, mul_one, hcard]
  have claim : ∀ k (hk : k < n), ENNReal.ofReal (∏ i, min (lam i) (lam ⟨k, hk⟩)) * volume C
      ≤ Gj n k (lam ⟨k, hk⟩ • C) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      intro hk
      have hk0 : k < n := by omega
      have hr : 0 ≤ (lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1)) := by
        have := hpos ⟨k + 1, hk⟩
        have := hpos ⟨k, hk0⟩
        positivity
      rw [hstep k hk0 hk, ENNReal.ofReal_mul hr, mul_assoc]
      calc ENNReal.ofReal ((lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1))) *
            (ENNReal.ofReal (∏ i, min (lam i) (lam ⟨k, hk0⟩)) * volume C)
          ≤ ENNReal.ofReal ((lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1))) *
            Gj n (k + 1) (lam ⟨k, hk0⟩ • C) := by
            gcongr
            exact (ih hk0).trans (hlev ⟨k, hk0⟩)
        _ ≤ Gj n (k + 1) (lam ⟨k + 1, hk⟩ • C) :=
            h4 n (k + 1) C (lam ⟨k, hk0⟩) (lam ⟨k + 1, hk⟩) hk.le hCo hCc hCs hCb (hpos _)
              (hmono (Fin.mk_le_mk.mpr (by omega)))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 := partialBoxVolumeTopLeOne 0 C
    rw [gjZero] at h0
    simp only [Fin.prod_univ_zero, mul_one]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h0)
  · have hn1 : n - 1 < n := by omega
    have hlast := (claim (n - 1) hn1).trans (hlev ⟨n - 1, hn1⟩)
    have htop := partialBoxVolumeTopLeOne n (lam ⟨n - 1, hn1⟩ • C)
    have e : ((⟨n - 1, hn1⟩ : Fin n) : ℕ) + 1 = n := by
      show n - 1 + 1 = n
      omega
    rw [e] at hlast
    have hprod : ∏ i, min (lam i) (lam ⟨n - 1, hn1⟩) = ∏ i, lam i :=
      Finset.prod_congr rfl fun i _ =>
        min_eq_left (hmono (Fin.le_def.mpr (show (i : ℕ) ≤ n - 1 by omega)))
    rw [hprod] at hlast
    have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg fun i _ => (hpos i).le
    have hfin : ENNReal.ofReal (∏ i, lam i) * volume C ≤ 1 := hlast.trans htop
    rw [mul_comm, ← ENNReal.toReal_ofReal hP, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hfin)

end Formalism.FN
