import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdeal

namespace FunctorialResolution.EmbeddedResolution

theorem tuningWeight_sub (m : ℕ) (c c' : ℕ → ℕ) (h : ∀ j, c' j ≤ c j) :
    tuningWeight m (fun j => c j - c' j) = tuningWeight m c - tuningWeight m c' := by
  have h2 : (fun j => (c j - c' j) + c' j) = c := funext fun j => Nat.sub_add_cancel (h j)
  have key : tuningWeight m (fun j => c j - c' j) + tuningWeight m c' = tuningWeight m c := by
    rw [← tuningWeight_fun_add m (fun j => c j - c' j) c', h2]
  omega

private theorem tuningWeight_ite (m j q : ℕ) (hj : j ∈ Finset.range m) :
    tuningWeight m (fun i => if i = j then q else 0) = (m - j) * q := by
  simp only [tuningWeight_eq_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hcon
    exact absurd hj hcon

theorem exists_le_tuningWeight_eq_mul (m L r : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (c : ℕ → ℕ)
    (hc : r * L + (m - 1) * L ≤ tuningWeight m c) :
    ∃ c' : ℕ → ℕ, (∀ j, c' j ≤ c j) ∧ tuningWeight m c' = r * L := by
  induction r generalizing c with
  | zero =>
      refine ⟨fun _ => 0, fun i => Nat.zero_le _, ?_⟩
      simp [tuningWeight_eq_sum]
  | succ r ih =>
      have hWpos : 0 < tuningWeight m c :=
        lt_of_lt_of_le (mul_pos (Nat.succ_pos r) hL) (le_trans (Nat.le_add_right _ _) hc)
      have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hWpos
          simp [tuningWeight_eq_sum] at hWpos
        · exact h0
      have hlt1 : ∀ a b : ℕ, a < b → a ≤ b - 1 := by
        intro a b h
        omega
      have hex : ∃ j ∈ Finset.range m, L ≤ (m - j) * c j := by
        by_contra hcon
        push Not at hcon
        have h1 : tuningWeight m c ≤ ∑ _x ∈ Finset.range m, (L - 1) := by
          rw [tuningWeight_eq_sum]
          refine Finset.sum_le_sum ?_
          intro i hi
          exact hlt1 _ _ (hcon i hi)
        have h2 : ∑ _x ∈ Finset.range m, (L - 1) = m * (L - 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        rw [h2] at h1
        have hA : m * (L - 1) + m = m * L := by
          have h' : L - 1 + 1 = L := Nat.sub_add_cancel hL
          calc m * (L - 1) + m = m * (L - 1 + 1) := by ring
            _ = m * L := by rw [h']
        have hB : (m - 1) * L + L = m * L := by
          have h' : m - 1 + 1 = m := Nat.sub_add_cancel hm
          calc (m - 1) * L + L = (m - 1 + 1) * L := by ring
            _ = m * L := by rw [h']
        have hC : L ≤ (r + 1) * L := by
          calc L = 1 * L := (one_mul L).symm
            _ ≤ (r + 1) * L := Nat.mul_le_mul (by omega) (le_refl L)
        have key : ∀ X Y Z W mm p : ℕ,
            X + Y ≤ Z → Z + mm = W → Y + p = W → p ≤ X → 1 ≤ mm → False := by
          intro X Y Z W mm p k1 k2 k3 k4 k5
          omega
        exact key ((r + 1) * L) ((m - 1) * L) (m * (L - 1)) (m * L) m L
          (le_trans hc h1) hA hB hC hm
      obtain ⟨j, hjmem, hjL⟩ := hex
      have hjm : j < m := Finset.mem_range.mp hjmem
      have hw0 : 0 < m - j := Nat.sub_pos_of_lt hjm
      have hw1 : 1 ≤ m - j := hw0
      obtain ⟨q, hq⟩ := hdvd (m - j) hw1 (Nat.sub_le m j)
      have hqc : q ≤ c j := by
        refine Nat.le_of_mul_le_mul_left ?_ hw0
        rw [← hq]
        exact hjL
      have hule : ∀ i, (if i = j then q else 0) ≤ c i := by
        intro i
        by_cases hij : i = j
        · rw [if_pos hij, hij]
          exact hqc
        · rw [if_neg hij]
          exact Nat.zero_le _
      have hu : tuningWeight m (fun i => if i = j then q else 0) = L := by
        rw [tuningWeight_ite m j q hjmem]
        exact hq.symm
      have hd : tuningWeight m (fun i => c i - (if i = j then q else 0)) = tuningWeight m c - L := by
        have h := tuningWeight_sub m c (fun i => if i = j then q else 0) hule
        rw [hu] at h
        exact h
      have hc2 : r * L + L + (m - 1) * L ≤ tuningWeight m c := by
        calc r * L + L + (m - 1) * L = (r + 1) * L + (m - 1) * L := by ring
          _ ≤ tuningWeight m c := hc
      have hc' : r * L + (m - 1) * L
          ≤ tuningWeight m (fun i => c i - (if i = j then q else 0)) := by
        rw [hd]
        have h9 : ∀ A B C W : ℕ, A + C + B ≤ W → A + B ≤ W - C := by
          intro A B C W h
          omega
        exact h9 _ _ _ _ hc2
      obtain ⟨e, he1, he2⟩ := ih (fun i => c i - (if i = j then q else 0)) hc'
      refine ⟨fun i => e i + (if i = j then q else 0), ?_, ?_⟩
      · intro i
        have h1 : e i ≤ c i - (if i = j then q else 0) := he1 i
        have h2 : (if i = j then q else 0) ≤ c i := hule i
        show e i + (if i = j then q else 0) ≤ c i
        by_cases hij : i = j
        · rw [if_pos hij] at h1 h2 ⊢
          omega
        · rw [if_neg hij] at h1 h2 ⊢
          omega
      · have hsplit : tuningWeight m (fun i => e i + (if i = j then q else 0))
            = tuningWeight m e + tuningWeight m (fun i => if i = j then q else 0) :=
          tuningWeight_fun_add m e (fun i => if i = j then q else 0)
        rw [hsplit, he2, hu]
        ring

section

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

theorem tunedIdeal_pow_le (J : Ideal S) (m a n : ℕ) :
    tunedIdeal k J m a ^ n ≤ tunedIdeal k J m (n * a) := by
  induction n with
  | zero => simp [tunedIdeal_zero]
  | succ n ih =>
      calc tunedIdeal k J m a ^ (n + 1)
          = tunedIdeal k J m a ^ n * tunedIdeal k J m a := pow_succ _ _
        _ ≤ tunedIdeal k J m (n * a) * tunedIdeal k J m a := Ideal.mul_mono ih le_rfl
        _ ≤ tunedIdeal k J m (n * a + a) := tunedIdeal_mul_le k J m _ _
        _ = tunedIdeal k J m ((n + 1) * a) := by
            rw [(by ring : n * a + a = (n + 1) * a)]

theorem tunedIdeal_mul_eq_tunedIdeal_add (J : Ideal S) (m L : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (r t : ℕ) (ht : (m - 1) * L ≤ t) :
    tunedIdeal k J m (r * L) * tunedIdeal k J m t = tunedIdeal k J m (r * L + t) := by
  refine le_antisymm (tunedIdeal_mul_le k J m _ _) ?_
  rw [tunedIdeal_le_iff]
  intro c hc
  have hc2 : r * L + (m - 1) * L ≤ tuningWeight m c :=
    le_trans (Nat.add_le_add_left ht (r * L)) hc
  obtain ⟨c', hc'le, hc'w⟩ := exists_le_tuningWeight_eq_mul m L r hL hdvd c hc2
  have h2 : (fun j => c' j + (c j - c' j)) = c := funext fun j => Nat.add_sub_cancel' (hc'le j)
  have hsplit : tuningMonomial k J m c' * tuningMonomial k J m (fun j => c j - c' j)
      = tuningMonomial k J m c := by
    rw [tuningMonomial_mul_fun_add k J m c' (fun j => c j - c' j), h2]
  rw [← hsplit]
  refine Ideal.mul_mono ?_ ?_
  · exact tuningMonomial_le_tunedIdeal k J m (r * L) c' (le_of_eq hc'w.symm)
  · refine tuningMonomial_le_tunedIdeal k J m t _ ?_
    rw [tuningWeight_sub m c c' hc'le, hc'w]
    have h9 : ∀ A B W : ℕ, A + B ≤ W → B ≤ W - A := by
      intro A B W h
      omega
    exact h9 (r * L) t (tuningWeight m c) hc

theorem tunedIdeal_pow_eq_tunedIdeal_mul (J : Ideal S) (m L : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (r : ℕ) (hr : m - 1 ≤ r) (j : ℕ) (hj : 1 ≤ j) :
    tunedIdeal k J m (r * L) ^ j = tunedIdeal k J m (j * (r * L)) := by
  induction j with
  | zero => exact absurd hj (by omega)
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have hn1 : 1 ≤ n := hn
        have ihn := ih hn1
        have hmt : (m - 1) * L ≤ n * (r * L) := by
          calc (m - 1) * L ≤ r * L := Nat.mul_le_mul hr (le_refl L)
            _ = 1 * (r * L) := (one_mul _).symm
            _ ≤ n * (r * L) := Nat.mul_le_mul hn1 (le_refl (r * L))
        calc tunedIdeal k J m (r * L) ^ (n + 1)
            = tunedIdeal k J m (r * L) ^ n * tunedIdeal k J m (r * L) := pow_succ _ _
          _ = tunedIdeal k J m (n * (r * L)) * tunedIdeal k J m (r * L) := by rw [ihn]
          _ = tunedIdeal k J m (r * L) * tunedIdeal k J m (n * (r * L)) := mul_comm _ _
          _ = tunedIdeal k J m (r * L + n * (r * L)) :=
              tunedIdeal_mul_eq_tunedIdeal_add k J m L hL hdvd r (n * (r * L)) hmt
          _ = tunedIdeal k J m ((n + 1) * (r * L)) := by
              rw [(by ring : r * L + n * (r * L) = (n + 1) * (r * L))]

theorem derivIdealIterate_tunedIdeal_pow_le (J : Ideal S) (m L : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (r : ℕ) (hr : m - 1 ≤ r) (i : ℕ) (hi : i < r * L) :
    derivIdealIterate k i (tunedIdeal k J m (r * L)) ^ (r * L) ≤
      tunedIdeal k J m (r * L) ^ (r * L - i) := by
  have hi' : 1 ≤ r * L - i := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hi)
  calc derivIdealIterate k i (tunedIdeal k J m (r * L)) ^ (r * L)
      ≤ tunedIdeal k J m (r * L - i) ^ (r * L) :=
        Ideal.pow_right_mono (derivIdealIterate_tunedIdeal_le k J m (r * L) i) (r * L)
    _ ≤ tunedIdeal k J m (r * L * (r * L - i)) := tunedIdeal_pow_le k J m (r * L - i) (r * L)
    _ = tunedIdeal k J m ((r * L - i) * (r * L)) := by
        rw [Nat.mul_comm (r * L) (r * L - i)]
    _ = tunedIdeal k J m (r * L) ^ (r * L - i) :=
        (tunedIdeal_pow_eq_tunedIdeal_mul k J m L hL hdvd r hr (r * L - i) hi').symm

end

end FunctorialResolution.EmbeddedResolution
