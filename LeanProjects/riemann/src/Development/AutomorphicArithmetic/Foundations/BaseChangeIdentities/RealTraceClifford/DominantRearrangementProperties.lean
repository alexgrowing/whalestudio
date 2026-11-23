import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem rearr_gap (n : ℕ) (a b : Fin n) : rhoV n a - rhoV n b = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
  simp only [rhoV]
  ring

private theorem sum_mul_perm_le_and_eq_one_of_antitone {n : ℕ} (x y : Fin n → ℝ) (hx : Antitone x) (hy : Antitone y) (w : Equiv.Perm (Fin n)) :
    ∑ a, x a * y (w a) ≤ ∑ a, x a * y a ∧
      (StrictAnti x → StrictAnti y → ∑ a, x a * y (w a) = ∑ a, x a * y a → w = 1) := by
  have hm : Monovary x y := hx.monovary hy
  refine ⟨hm.sum_mul_comp_perm_le_sum_mul, fun sx sy he => ?_⟩
  have h2 := hm.sum_mul_comp_perm_eq_sum_mul_iff.1 he
  have hmono : StrictMono w := by
    intro i j hij
    by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hlt | heq
    · exact absurd (h2 (show y (w i) < y (w j) from sy hlt)) (not_le.2 (sx hij))
    · exact absurd (w.injective heq) (ne_of_gt hij)
  have := hmono.eq_id
  ext i
  simp [this]

private theorem rearr_lemma_2 {n : ℕ} (x : Fin n → ℝ) :
    Antitone (domC x) ∧ (∃ w : Equiv.Perm (Fin n), domC x = x ∘ w) ∧ (Antitone x → domC x = x) ∧
      (∀ w : Equiv.Perm (Fin n), domC (x ∘ w) = domC x) ∧ nsq (domC x) = nsq x := by
  refine ⟨?_, ⟨_, rfl⟩, fun hx => ?_, fun w => ?_, ?_⟩
  · intro a b hab
    have := Tuple.monotone_sort (fun a => -x a) hab
    simpa [domC] using this
  · have : Tuple.sort (fun a => -x a) = Equiv.refl (Fin n) :=
      Tuple.sort_eq_refl_iff_monotone.2 (fun a b hab => neg_le_neg (hx hab))
    simp [domC, this]
  · have h := Tuple.comp_perm_comp_sort_eq_comp_sort (f := fun a => -x a) (σ := w)
    funext a
    show (x ∘ w) ((Tuple.sort ((fun a => -x a) ∘ w)) a) = x ((Tuple.sort fun a => -x a) a)
    have := congrFun h a
    simp only [Function.comp_apply, neg_inj] at this
    exact this
  · unfold nsq domC
    exact Equiv.sum_comp (Tuple.sort fun a => -x a) (fun a => x a ^ 2)

private theorem strictAnti_rhoV_and_dom_rhoV (n : ℕ) : StrictAnti (rhoV n) ∧ Dom (rhoV n) := by
  constructor
  · intro a b hab
    have h1 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith [rearr_gap n a b]
  · unfold Dom
    intro a b hab
    refine ⟨(b : ℕ) - (a : ℕ), ?_⟩
    rw [rearr_gap, Nat.cast_sub (Fin.lt_def.mp hab).le]

private theorem antitone_and_dom_domC_sub_rhoV_of_dom (n : ℕ) (x : Wt n) (hx : Dom x) : Antitone x ∧ Dom (domC (x - rhoV n)) := by
  unfold Dom at hx
  have hint : ∀ a b, ∃ k : ℤ, (x - rhoV n) a - (x - rhoV n) b = k := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨m, hm⟩ := hx a b h
      refine ⟨(m : ℤ) - ((b : ℕ) : ℤ) + ((a : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply]
      push_cast
      linarith [rearr_gap n a b]
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨m, hm⟩ := hx b a h
      refine ⟨-(m : ℤ) + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply]
      push_cast
      linarith [rearr_gap n b a]
  refine ⟨fun a b hab => ?_, ?_⟩
  · rcases hab.lt_or_eq with h | h
    · obtain ⟨m, hm⟩ := hx a b h
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · rw [h]
  · unfold Dom
    intro a b hab
    obtain ⟨w, hw⟩ := (rearr_lemma_2 (x - rhoV n)).2.1
    have hanti := (rearr_lemma_2 (x - rhoV n)).1
    obtain ⟨k, hk⟩ := hint (w a) (w b)
    have hk0 : (0 : ℝ) ≤ k := by
      have := hanti hab.le
      rw [hw] at this
      simp only [Function.comp_apply] at this
      linarith
    have hk1 : (0 : ℤ) ≤ k := by exact_mod_cast hk0
    refine ⟨k.toNat, ?_⟩
    rw [hw]
    simp only [Function.comp_apply]
    rw [hk, ← Int.cast_natCast, Int.toNat_of_nonneg hk1]

private theorem nsq_le_and_eq_of_nsq_le_sum_mul {n : ℕ} (x y : Fin n → ℝ) (h : nsq x ≤ ∑ a, x a * y a) :
    nsq x ≤ nsq y ∧ (nsq y ≤ nsq x → x = y) := by
  have hsq : 0 ≤ ∑ a, (x a - y a) ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hexp : ∑ a, (x a - y a) ^ 2 = nsq x - 2 * ∑ a, x a * y a + nsq y := by
    unfold nsq
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  refine ⟨by linarith, fun h2 => ?_⟩
  have h0 : ∑ a, (x a - y a) ^ 2 = 0 := by linarith
  funext a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (x a - y a))).1 h0 a (Finset.mem_univ a)
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

theorem UpperTheory.RealTr.rearr :
    ∀ n : ℕ, (∀ x y : Wt n, Antitone x → Antitone y → ∀ w : Equiv.Perm (Fin n), ∑ a, x a * y (w a) ≤ ∑ a, x a * y a ∧
        (StrictAnti x → StrictAnti y → ∑ a, x a * y (w a) = ∑ a, x a * y a → w = 1)) ∧
      (∀ x : Wt n, Antitone (domC x) ∧ (∃ w : Equiv.Perm (Fin n), domC x = x ∘ w) ∧ (Antitone x → domC x = x) ∧
        (∀ w : Equiv.Perm (Fin n), domC (x ∘ w) = domC x) ∧ nsq (domC x) = nsq x) ∧
      StrictAnti (rhoV n) ∧ Dom (rhoV n) ∧ (∀ x : Wt n, Dom x → Antitone x ∧ Dom (domC (x - rhoV n))) ∧
      ∀ x y : Wt n, nsq x ≤ ∑ a, x a * y a → nsq x ≤ nsq y ∧ (nsq y ≤ nsq x → x = y) := by
  intro n
  exact ⟨fun x y hx hy w => sum_mul_perm_le_and_eq_one_of_antitone x y hx hy w, fun x => rearr_lemma_2 x, (strictAnti_rhoV_and_dom_rhoV n).1, (strictAnti_rhoV_and_dom_rhoV n).2,
    fun x hx => antitone_and_dom_domC_sub_rhoV_of_dom n x hx, fun x y h => nsq_le_and_eq_of_nsq_le_sum_mul x y h⟩
