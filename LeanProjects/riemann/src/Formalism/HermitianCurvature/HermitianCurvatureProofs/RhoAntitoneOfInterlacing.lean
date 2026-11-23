import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount

open Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P

theorem lambda_side_inequality : C7.LamSide := by
  unfold C7.LamSide C7.LamInterlaces
  rintro k r u u' lam l Y hl hlk ⟨hA, hL⟩ ⟨-, hL'⟩ - i
  constructor
  · intro hli
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 1 := ⟨⟨l - 1, by omega⟩, rfl⟩
    have hji : j ≤ i := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam i ≤ lam j := hA.antitone hji
    have h1 := (hL j).1 (by omega)
    have h2 := (hL' j).1 (by omega)
    rw [show (j : ℕ) + 1 = l by omega] at h1 h2
    exact lt_min (lt_of_le_of_lt hi1 h1) (lt_of_le_of_lt hi1 h2)
  · intro hil
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 2 := ⟨⟨l - 2, by omega⟩, rfl⟩
    have hij : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam j ≤ lam i := hA.antitone hij
    have h1 := (hL j).2 (by omega)
    have h2 := (hL' j).2 (by omega)
    rw [show (j : ℕ) + 2 = l by omega] at h1 h2
    exact max_lt (lt_of_lt_of_le h1 hi1) (lt_of_lt_of_le h2 hi1)

theorem rho_antitone_of_interlacing {k : ℕ} {u u' ρ : ℕ → ℝ} (h : I.Interlaces k u u' ρ) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k - 1 → ρ j ≤ ρ i := by
  intro i j hi hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih =>
    have h1 := h n (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := h (n + 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h3 := ih (by omega)
    linarith [h1.2.2.1, h2.1]

theorem rho_side_inequality : C7.RhoSide := by
  unfold C7.RhoSide C7.Between
  intro k u u' ρ l Y hl hlk hI hB i hi
  have hi' : 1 ≤ i ∧ i ≤ k - 1 := by simpa using hi
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · intro hli
    have h1 := hI l (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI l i hl hli hi'.2
    have h3 : ρ l + 1 / 2 ≤ min (u l) (u' l) := le_min h1.1 h1.2.1
    linarith
  · intro hil
    have h1 := hI (l - 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI i (l - 1) hi'.1 (by omega) (by omega)
    rw [show l - 1 + 1 = l by omega] at h1
    have h3 : max (u l) (u' l) + 1 / 2 ≤ ρ (l - 1) := by
      rcases le_total (u l) (u' l) with h | h
      · rw [max_eq_right h]; exact h1.2.2.2
      · rw [max_eq_left h]; exact h1.2.2.1
    linarith

theorem sign_change_count : C7.SignCount := by
  unfold C7.SignCount
  intro ι _ f S hS hne
  classical
  rw [← Finset.prod_mul_prod_compl S f, ← mul_assoc]
  have h1 : (-1 : ℝ) ^ S.card * ∏ i ∈ S, f i = ∏ i ∈ S, (-f i) := by
    rw [Finset.prod_neg]
  rw [h1]
  apply mul_pos
  · exact Finset.prod_pos fun i hi => by linarith [(hS i).1 hi]
  · refine Finset.prod_pos fun i hi => ?_
    have h2 : ¬ f i < 0 := fun h => (Finset.mem_compl.1 hi) ((hS i).2 h)
    exact lt_of_le_of_ne (not_lt.1 h2) (hne i).symm

theorem sign_prod_of_split_at_index (s : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) (hpos : ∀ j ∈ s, j < m → 0 < g j)
    (hneg : ∀ j ∈ s, m ≤ j → g j < 0) : 0 < (-1 : ℝ) ^ (s.filter (m ≤ ·)).card * ∏ j ∈ s, g j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
      (fun j hj => hneg j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert ha, Finset.filter_insert]
    by_cases hma : m ≤ a
    · rw [if_pos hma, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1), pow_succ]
      have := hneg a (Finset.mem_insert_self a s) hma
      nlinarith
    · rw [if_neg hma]
      have := hpos a (Finset.mem_insert_self a s) (by omega)
      nlinarith

theorem polynomial_sign : C7.PSign := by
  unfold C7.PSign
  intro k r u u' ρ lam l Y hl hlk hL hL' hI hB
  have hside := lambda_side_inequality k r u u' lam l Y hl hlk hL hL' hB
  have hrho := rho_side_inequality k u u' ρ l Y hl hlk hI hB
  have hB' := hB
  unfold C7.Between at hB'
  have hA : 0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) := by
    have hprod : ∏ s, (Y + lam s) = ∏ j ∈ Finset.range (k + 2 * r + 1),
        (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) j := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [dif_pos s.isLt, Fin.eta]
    have key := sign_prod_of_split_at_index (Finset.range (k + 2 * r + 1))
      (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) (l - 1)
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).2 (show j + 1 < l by omega)
        linarith [hB'.2])
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).1 (show l ≤ j + 1 by omega)
        linarith [hB'.1])
    have hcard : ((Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·)).card = (k - l) + 2 * (r + 1) := by
      rw [(show (Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·) = Finset.Ico (l - 1) (k + 2 * r + 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega), Nat.card_Ico]
      omega
    rw [hcard, pow_add, pow_mul, neg_one_sq, one_pow, mul_one] at key
    rw [hprod]
    exact key
  have hB2 : 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y := by
    unfold I.xpoly
    have key := sign_prod_of_split_at_index (Finset.Icc 1 (k - 1)) (fun i => Y + ρ i) l
      (fun i hi hil => show 0 < Y + ρ i by linarith [(hrho i hi).2 hil])
      (fun i hi hli => show Y + ρ i < 0 by linarith [(hrho i hi).1 hli])
    have hcard : ((Finset.Icc 1 (k - 1)).filter (l ≤ ·)).card = k - l := by
      rw [(show (Finset.Icc 1 (k - 1)).filter (l ≤ ·) = Finset.Icc l (k - 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega), Nat.card_Icc]
      omega
    rw [hcard] at key
    exact key
  refine ⟨hA, hB2, ?_⟩
  have h := abs_of_pos hA
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
  exact h

theorem polynomial_sign_of_parts : C7.PSignOfParts := fun _ _ _ => polynomial_sign

theorem roots_outside_jointly : C7.RootsOutJoint := by
  unfold C7.RootsOutJoint LE.Sys.RootsOut
  intro S u u' l hl hlk hI hI' hB s hs
  have hb := hB _ hs
  have key := lambda_side_inequality S.k S.r u u' S.lam l (-S.lam s) hl hlk hI hI' hb s
  unfold C7.Between at hb
  rw [neg_neg] at hb
  by_cases h : l ≤ s.val + 1
  · have := key.1 h
    linarith [hb.1]
  · have := key.2 (by omega)
    linarith [hb.2]

theorem roots_outside_of_parts : C7.RootsOutOfParts := fun _ => roots_outside_jointly

theorem interlacing_of_parts : C7.LemmaEInterlacingOfParts := by
  unfold C7.LemmaEInterlacingOfParts C7.LemmaEInterlacing LE.LemmaE
  intro hE hR CR Cd CP h1 h2 h3 C₂ hC₂ C₆ hC₆ S u u' l hl hlk hI hI' hB hN hL hβ
  exact hE CR Cd CP h1 h2 h3 C₂ hC₂ C₆ hC₆ S hN hL hβ (hR S u u' l hl hlk hI hI' hB)

end Formalism.FourierDecayAlt.P
