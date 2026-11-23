import Formalism.HermitianCurvature.StatementI

namespace Formalism.FourierDecayAlt.P.Interlace

open Finset Formalism.FourierDecayAlt.I

lemma interlaces_swap {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    Interlaces k u' u ρ := by
  intro i hi
  obtain ⟨a, b, c, d⟩ := h i hi
  exact ⟨b, a, d, c⟩

lemma antitone_on {f : ℕ → ℝ} {k : ℕ} (h : ∀ i, 1 ≤ i → i + 1 ≤ k → f (i + 1) ≤ f i) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → f j ≤ f i := by
  intro i j hi hij hjk
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact (h n (by omega) hjk).trans (ih (by omega))

lemma u_step {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    ∀ i, 1 ≤ i → i + 1 ≤ k → u (i + 1) ≤ u i := by
  intro i h1 h2
  obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨h1, by omega⟩)
  linarith

lemma sign_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) (e : ℝ)
    (he : -1 ≤ e ∧ e ≤ 1) :
    0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hcard : (filter (fun i => ¬ i < l) (Icc 1 (k - 1))).card = k - l := by
    have : filter (fun i => ¬ i < l) (Icc 1 (k - 1)) = Icc l (k - 1) := by
      ext i; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc]; omega
  have key : (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) =
      ∏ i ∈ Icc 1 (k - 1), ((if i < l then (1 : ℝ) else -1) * (Y + e + ρ i)) := by
    rw [prod_mul_distrib, prod_ite, prod_const_one, one_mul, prod_const, hcard]
    rfl
  rw [key]
  apply prod_pos
  intro i hi
  have hi' := mem_Icc.1 hi
  obtain ⟨a, b, c, d⟩ := h i hi
  split_ifs with hil
  · have := hu' (i + 1) l (by omega) (by omega) hlk
    rw [one_mul]; linarith
  · have := hu l i hl1 (by omega) (by omega)
    rw [neg_one_mul]; linarith

theorem interlaceSign : InterlaceSign := by
  intro k u u' ρ l Y hl1 hlk h hc e he
  have he' : -1 ≤ e ∧ e ≤ 1 := by
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> norm_num
  rcases hc with hA | hB
  · exact sign_core k u u' ρ l Y hl1 hlk h hA e he'
  · exact sign_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB e he'

lemma q_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  rw [← mul_prod_erase _ _ hl]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos <;> linarith
  · apply prod_pos
    intro i hi
    have hne := ne_of_mem_erase hi
    have hi' := mem_Icc.1 (mem_of_mem_erase hi)
    rcases lt_or_gt_of_ne hne with hil | hil
    · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi'.1, by omega⟩)
      have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      have h2 := hu' i l hi'.1 (by omega) hlk
      apply mul_pos <;> linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
      have h1 := hu l (j + 1) hl1 (by omega) hi'.2
      have h2 := hu l j hl1 (by omega) (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith

theorem qPositive : QPositive := by
  intro k u u' ρ l Y T T' hl1 hlk h hc hT hT'
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hP : ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
    rcases hc with hA | hB
    · exact q_core k u u' ρ l Y hl1 hlk h hA
    · have := q_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
      rwa [prod_congr rfl (fun i _ => mul_comm (Y + 1/2 + u' i) (Y + 1/2 + u i))] at this
  unfold qpoly
  nlinarith

lemma ratio_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    xpoly k ρ (Y + 1) ^ 2 * (|Y + 1/2 + u l| * |Y + 1/2 + u' l|) ≤
      |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  set g : ℕ → ℝ := fun j => |Y + 1/2 + u j| * |Y + 1/2 + u' j| with hg
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  have hR : |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| =
      g l * ∏ i ∈ Icc 1 (k - 1), g (if i < l then i else i + 1) := by
    rw [abs_mul, abs_prod, abs_prod, ← prod_mul_distrib, ← mul_prod_erase _ _ hl]
    congr 1
    symm
    apply prod_nbij' (fun i => if i < l then i else i + 1) (fun j => if j < l then j else j - 1)
    · intro a ha
      simp only [mem_Icc] at ha
      simp only [mem_erase, mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      simp only [mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      rfl
  rw [hR, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold xpoly
  rw [← prod_pow]
  apply prod_le_prod
  · intro i _; positivity
  · intro i hi
    have hi' := mem_Icc.1 hi
    obtain ⟨a, b, c, d⟩ := h i hi
    simp only [hg]
    split_ifs with hil
    · have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      nlinarith
    · have h1 := hu l i hl1 (by omega) (by omega)
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      nlinarith

theorem interlaceRatio : InterlaceRatio := by
  intro k u u' ρ l Y hl1 hlk h hc
  rcases hc with hA | hB
  · exact ratio_core k u u' ρ l Y hl1 hlk h hA
  · have := ratio_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
    rwa [mul_comm (|Y + 1/2 + u' l|), mul_comm (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))] at this

end Formalism.FourierDecayAlt.P.Interlace

theorem Formalism.FourierDecayAlt.P.interlacing_sign : Formalism.FourierDecayAlt.I.InterlaceSign := Formalism.FourierDecayAlt.P.Interlace.interlaceSign
theorem Formalism.FourierDecayAlt.P.q_positive_interlacing : Formalism.FourierDecayAlt.I.QPositive := Formalism.FourierDecayAlt.P.Interlace.qPositive
theorem Formalism.FourierDecayAlt.P.interlacing_ratio : Formalism.FourierDecayAlt.I.InterlaceRatio := Formalism.FourierDecayAlt.P.Interlace.interlaceRatio
