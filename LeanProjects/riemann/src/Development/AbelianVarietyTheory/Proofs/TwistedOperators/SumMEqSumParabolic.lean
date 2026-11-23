import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsilonSumLeviZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsilonAlternatingSumZeroStatement

noncomputable section

open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace Classical

namespace GlobalTheory.Chamber.FourierIdGeneric

variable {k : ℕ}

theorem epsOf_empty (b : SV k → A0 k) (l : A0 k) : epsOf ∅ b l = 1 := by
  have : IsEmpty ↥(∅ : Finset (SV k)) := ⟨fun x => Finset.notMem_empty _ x.2⟩
  rw [epsOf, Matrix.det_isEmpty]; simp

theorem eps_self (S : Finset (SV k)) (l : A0 k) : eps S S l = 1 := by
  simp only [eps, sdiff_self, bot_eq_empty, epsOf_empty]

theorem epsHat_self (S : Finset (SV k)) (l : A0 k) : epsHat S S l = 1 := by
  simp only [epsHat, sdiff_self, bot_eq_empty, epsOf_empty]

theorem sum_swap (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (g : Finset (SV k) → Finset (SV k) → ℂ) :
    ∑ P ∈ parP 𝔞 Q, ∑ R ∈ between P Q, g P R = ∑ R ∈ parF 𝔞 Q, ∑ P ∈ parP 𝔞 R, g P R := by
  refine Finset.sum_comm' fun P R => ?_
  simp only [mem_parP, mem_parF, between, mem_filter, mem_powerset]
  constructor
  · rintro ⟨⟨hP, ha, -⟩, hRP, hQR⟩
    exact ⟨⟨hP, ha, hRP⟩, hP.mono hRP, ha ▸ vecSpan_mono hRP, hQR⟩
  · rintro ⟨⟨hP, ha, hRP⟩, -, -, hQR⟩
    exact ⟨⟨hP, ha, hQR.trans hRP⟩, hRP, hQR⟩

theorem parP_self {𝔞 : Submodule ℝ (A0 k)} {S : Finset (SV k)} (hS : IsPar S) (h : aP S = 𝔞) :
    parP 𝔞 S = {S} := by
  ext P
  rw [mem_parP, mem_singleton]
  constructor
  · rintro ⟨hP, ha, hSP⟩
    refine Subset.antisymm (fun u hu => ?_) hSP
    by_contra hu'
    refine hP.vec_notMem hu (vecSpan_mono (fun v hv => mem_erase.2 ⟨fun e => hu' (by subst e; exact hv), hSP hv⟩) ?_)
    rw [h, ← ha]
    exact Submodule.subset_span ⟨u, hu, rfl⟩
  · rintro rfl; exact ⟨hS, h, subset_rfl⟩

theorem filter_parF (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) :
    (parF 𝔞 Q).filter (fun R => aP R = 𝔞) = parP 𝔞 Q := by
  ext R
  simp only [mem_filter, mem_parF, mem_parP]
  constructor
  · rintro ⟨⟨a, -, c⟩, d⟩; exact ⟨a, d, c⟩
  · rintro ⟨a, d, c⟩; exact ⟨⟨a, d.le, c⟩, d⟩

def coefA (𝔞 : Submodule ℝ (A0 k)) (S : Finset (SV k)) (l : A0 k) : ℂ :=
  ∑ P ∈ parP 𝔞 S, (-1 : ℂ) ^ (P \ S).card * epsHat P S l

theorem coefA_of_eq {𝔞 : Submodule ℝ (A0 k)} {S : Finset (SV k)} (hS : IsPar S) (h : aP S = 𝔞) (l : A0 k) :
    coefA 𝔞 S l = 1 := by
  rw [coefA, parP_self hS h, sum_singleton, sdiff_self, bot_eq_empty, card_empty, pow_zero, one_mul, epsHat_self]

theorem coefA_eq_zero {𝔞 : Submodule ℝ (A0 k)} (h𝔞 : IsLevi 𝔞) {l : A0 k} (hl : l ∈ generic k) :
    ∀ S ∈ parF 𝔞 ∅, aP S ≠ 𝔞 → coefA 𝔞 S l = 0 := by
  suffices H : ∀ n, ∀ S, Fintype.card (SV k) - S.card = n → S ∈ parF 𝔞 ∅ → aP S ≠ 𝔞 → coefA 𝔞 S l = 0 from
    fun S hS ha => H _ S rfl hS ha
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hS ha
  have hS' := mem_parF.1 hS
  have h0 : ∑ R ∈ parF 𝔞 S, coefA 𝔞 R l * eps R S l = 0 := by
    calc ∑ R ∈ parF 𝔞 S, coefA 𝔞 R l * eps R S l
        = ∑ P ∈ parP 𝔞 S, ∑ R ∈ between P S, (-1 : ℂ) ^ (P \ R).card * epsHat P R l * eps R S l := by
          rw [sum_swap 𝔞 S (fun P R => (-1 : ℂ) ^ (P \ R).card * epsHat P R l * eps R S l)]
          simp only [coefA, sum_mul]
      _ = 0 := by
          refine sum_eq_zero fun P hP => ?_
          obtain ⟨hP1, hP2, hP3⟩ := mem_parP.1 hP
          exact GlobalTheory.T.epsilon_alternating_sum_zero k P S hP1 hP3 (by rintro rfl; exact ha hP2) l hl
  rw [← sum_filter_add_sum_filter_not (parF 𝔞 S) (fun R => aP R = 𝔞)] at h0
  have h2 : ∑ R ∈ (parF 𝔞 S).filter (fun R => aP R = 𝔞), coefA 𝔞 R l * eps R S l = 0 := by
    rw [filter_parF, ← GlobalTheory.T.epsilon_sum_levi_zero k 𝔞 S h𝔞 hS ha l hl]
    refine sum_congr rfl fun R hR => ?_
    obtain ⟨a, d, -⟩ := mem_parP.1 hR
    rw [coefA_of_eq a d, one_mul]
  have h3 : ∑ R ∈ (parF 𝔞 S).filter (fun R => ¬ aP R = 𝔞), coefA 𝔞 R l * eps R S l = coefA 𝔞 S l := by
    rw [sum_eq_single S]
    · rw [eps_self, mul_one]
    · intro R hR hne
      obtain ⟨hR1, hR2⟩ := mem_filter.1 hR
      obtain ⟨a, b, c⟩ := mem_parF.1 hR1
      have hss : S ⊂ R := ssubset_of_subset_of_ne c (Ne.symm hne)
      have h4 := card_lt_card hss
      have h5 := card_le_univ R
      rw [ih (Fintype.card (SV k) - R.card) (by omega) R rfl (mem_parF.2 ⟨a, b, empty_subset _⟩) hR2, zero_mul]
    · intro h
      exact absurd (mem_filter.2 ⟨mem_parF.2 ⟨hS'.1, hS'.2.1, subset_rfl⟩, ha⟩) h
  rw [h2, h3, zero_add] at h0
  exact h0

end GlobalTheory.Chamber.FourierIdGeneric

open GlobalTheory.Chamber.FourierIdGeneric in

theorem GlobalTheory.Chamber.sumM_eq_sum_sumP : ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)), IsLevi 𝔞 →
    Q ∈ parF 𝔞 ∅ → ∀ (c : Finset (SV k) → A0 k → ℂ), ∀ l ∈ generic k,
    sumM 𝔞 Q c l = ∑ P ∈ parP 𝔞 Q, sumP P Q c l := by
  intro k 𝔞 Q h𝔞 hQ c l hl
  have e1 : ∑ P ∈ parP 𝔞 Q, sumP P Q c l = ∑ S ∈ parF 𝔞 Q, coefA 𝔞 S l * (eps S Q l * c S l) := by
    simp only [sumP]
    rw [sum_swap 𝔞 Q (fun P S => (-1 : ℂ) ^ (P \ S).card * epsHat P S l * eps S Q l * c S l)]
    simp only [coefA, sum_mul]
    refine sum_congr rfl fun S _ => sum_congr rfl fun P _ => by ring
  have e2 : ∑ S ∈ (parF 𝔞 Q).filter (fun S => ¬ aP S = 𝔞), coefA 𝔞 S l * (eps S Q l * c S l) = 0 := by
    refine sum_eq_zero fun S hS => ?_
    obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
    obtain ⟨a, b, -⟩ := mem_parF.1 hS1
    rw [coefA_eq_zero h𝔞 hl S (mem_parF.2 ⟨a, b, empty_subset _⟩) hS2, zero_mul]
  rw [e1, ← sum_filter_add_sum_filter_not (parF 𝔞 Q) (fun S => aP S = 𝔞), e2, add_zero, filter_parF, sumM]
  refine sum_congr rfl fun S hS => ?_
  obtain ⟨a, d, -⟩ := mem_parP.1 hS
  rw [coefA_of_eq a d, one_mul]

example : ∀ (k : ℕ) (𝔞 : Submodule ℝ (GlobalTheory.Chamber.A0 k)) (Q : Finset (GlobalTheory.Chamber.SV k)), IsLevi 𝔞 → Q ∈ parF 𝔞 ∅ → ∀ (c : Finset (SV k) → A0 k → ℂ), ∀ l ∈ generic k, sumM 𝔞 Q c l = ∑ P ∈ parP 𝔞 Q, sumP P Q c l := GlobalTheory.Chamber.sumM_eq_sum_sumP
