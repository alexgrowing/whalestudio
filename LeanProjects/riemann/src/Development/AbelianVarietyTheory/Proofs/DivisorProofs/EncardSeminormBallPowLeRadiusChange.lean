import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatedSetCoversSeminormBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPowLeEncardSeminormBallDigitSums

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

set_option autoImplicit false in
open Filter Topology in
private lemma isBallFam_mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {r r' : ℝ} (hrr' : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.2 hrr'))
  simpa using this

set_option autoImplicit false in
open Filter Topology in
private lemma encard_mul_encard_le_isBallFam {G : Type} [AddCommGroup G] {Λ : AddSubgroup G}
    {B : ℝ → Set G} (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (hbm : b + b ≤ m) (hfa : (B a).Finite) (hfb : (B b).Finite) (hf1 : (B 1).Finite) :
    (B a).encard * (B b).encard ≤ (B 1).encard * (B (m * a + b)).encard := by
  classical
  set S := hfa.toFinset ×ˢ hfb.toFinset with hS
  let f : G × G → G := fun p ↦ m • p.1 + p.2
  have hmem : ∀ p ∈ S, f p ∈ B (m * a + b) := by
    intro p hp
    rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    have h1 : m • p.1 ∈ B (m * a) :=
      (hB.nsmul_iff m a p.1 hm (hB.subset a hp.1)).2 hp.1
    have h2 : -p.2 ∈ B (0 + b) := by
      simpa using hB.sub_mem 0 b 0 p.2 (hB.zero_mem 0 le_rfl) hp.2
    have := hB.sub_mem _ _ _ _ h1 h2
    simpa [f, sub_neg_eq_add] using this
  have hcard : S.card ≤ hf1.toFinset.card * (S.image f).card := by
    refine Finset.card_le_mul_card_image S _ fun w hw ↦ ?_
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hw
    refine Finset.card_le_card_of_injOn (fun p ↦ p₀.1 - p.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hp
      obtain ⟨hpS, hfp⟩ := hp
      have hp₀' := hp₀
      rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hpS hp₀'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      have hd : m • (p₀.1 - p.1) = p.2 - p₀.2 := by
        simp only [f] at hfp
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← hfp]
        abel
      have hΛ : p₀.1 - p.1 ∈ Λ := Λ.sub_mem (hB.subset a hp₀'.1) (hB.subset a hpS.1)
      have h2 : p.2 - p₀.2 ∈ B ((m : ℝ) * 1) :=
        isBallFam_mono hB (by simpa using hbm) (hB.sub_mem _ _ _ _ hpS.2 hp₀'.2)
      exact (hB.nsmul_iff m 1 _ hm hΛ).1 (hd ▸ h2)
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := by simpa using hpq
      have h2 : p.2 = q.2 := by
        have := hp.2.trans hq.2.symm
        simp only [f, h1] at this
        exact add_left_cancel this
      exact Prod.ext h1 h2
  have himg : ((S.image f).card : ℕ∞) ≤ (B (m * a + b)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard fun w hw ↦ ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
    exact hmem p hp
  rw [hfa.encard_eq_coe_toFinset_card, hfb.encard_eq_coe_toFinset_card,
    hf1.encard_eq_coe_toFinset_card, ← Nat.cast_mul, ← Finset.card_product]
  calc ((S.card : ℕ) : ℕ∞) ≤ ((hf1.toFinset.card * (S.image f).card : ℕ) : ℕ∞) := by
        exact_mod_cast hcard
    _ ≤ (hf1.toFinset.card : ℕ∞) * (B (m * a + b)).encard := by
        push_cast
        gcongr

open Filter Topology in

theorem _root_.GlobalTheory.VolBr.encard_ball_pow_le : ∀ (G : Type) [AddCommGroup G]
    (Λ : AddSubgroup G) (B : ℝ → Set G), _root_.GlobalTheory.VolBr.IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ),
    1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite →
    (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  intro G _ Λ B hB R Q e hR hQ hfin
  have h1 : (B 1).Finite := hfin.subset (isBallFam_mono hB hR)
  have hQ2 : (2 : ℝ) ≤ Q := by linarith
  have hB1 : (B 1).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.1 ⟨0, hB.zero_mem 1 zero_le_one⟩
  by_cases hbig : (B (R * Q ^ e)).Finite
  swap
  · rw [Set.Infinite.encard_eq hbig, ENat.mul_top (pow_ne_zero _ hB1)]
    exact le_top
  set s : ℕ → ℝ := fun j ↦ ∑ i ∈ Finset.range j, (Q : ℝ) ^ i with hs
  have hs_succ : ∀ j, s (j + 1) = Q * s j + 1 := by
    intro j
    simp only [hs, Finset.sum_range_succ', pow_succ, pow_zero, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hs_nonneg : ∀ j, 0 ≤ s j := fun j ↦ Finset.sum_nonneg fun i _ ↦ by positivity
  have hs_le : ∀ j, s j + 1 ≤ (Q : ℝ) ^ j := by
    intro j
    induction j with
    | zero => simp [hs]
    | succ j ih =>
      rw [hs_succ, pow_succ]
      nlinarith [hs_nonneg j]
  have hclaim : ∀ j ≤ e, (B R).encard ^ j ≤ (B 1).encard ^ j * (B (R * s j)).encard := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [pow_zero, one_mul, hs, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact Set.one_le_encard_iff_nonempty.2 ⟨0, hB.zero_mem 0 le_rfl⟩
    | succ j ih =>
      intro hj
      have hRs : R * s j ≤ R * Q ^ e := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        calc s j ≤ (Q : ℝ) ^ j := by linarith [hs_le j]
          _ ≤ (Q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      have hfs : (B (R * s j)).Finite := hbig.subset (isBallFam_mono hB hRs)
      have hQpos : 0 < Q := by exact_mod_cast (show (0 : ℝ) < Q by linarith)
      have step := encard_mul_encard_le_isBallFam hB (a := R * s j) (b := R) hQpos (by linarith)
        hfs hfin h1
      have hrad : (Q : ℝ) * (R * s j) + R = R * s (j + 1) := by rw [hs_succ]; ring
      rw [hrad] at step
      calc (B R).encard ^ (j + 1) = (B R).encard ^ j * (B R).encard := pow_succ _ _
        _ ≤ (B 1).encard ^ j * (B (R * s j)).encard * (B R).encard := by
            gcongr; exact ih (by omega)
        _ = (B 1).encard ^ j * ((B (R * s j)).encard * (B R).encard) := mul_assoc _ _ _
        _ ≤ (B 1).encard ^ j * ((B 1).encard * (B (R * s (j + 1))).encard) := by gcongr
        _ = (B 1).encard ^ (j + 1) * (B (R * s (j + 1))).encard := by rw [pow_succ, mul_assoc]
  calc (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * s e)).encard := hclaim e le_rfl
    _ ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
        gcongr
        exact isBallFam_mono hB (mul_le_mul_of_nonneg_left (by linarith [hs_le e]) (by linarith))

end GlobalTheory.VolBr
