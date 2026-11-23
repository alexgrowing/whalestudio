import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotalCochainOfDegreeSuccOfDifferentialsStatement

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem delta_topPart_eq_zero {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E)
    (c : Finset ι → E) (k : ℕ) (hc : Dtot d c = 0) (hk : ∀ s, k < s.card → c s = 0) :
    delta (fun s => if s.card = k then c s else 0) = 0 := by
  funext t
  by_cases ht : t.card = k + 1
  · have h1 : delta c t = 0 := by
      have h := congrFun hc t
      simpa [Dtot, hk t (by omega)] using h
    rw [Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : (t.erase i).card = k := by rw [Finset.card_erase_of_mem hi]; omega
    simp only [this, if_true]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have h0 := Finset.card_erase_add_one hi
    have : (t.erase i).card ≠ k := by omega
    simp only [this, if_false, smul_zero]

theorem hypZero_of_cechZero : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → ∀ n, (∀ q b, q + b = n → CechZero (T q) b) → HypZero d T n := by
  intro ι _ E _ d T hdd hmono hdT n hC
  obtain ⟨-, -, hadd, hsub, -, hDD⟩ := GlobalTheory.T.cech_and_total_differential_additive_square_zero (ι := ι) d
  have key : ∀ k, k ≤ n + 1 → ∀ c, InTot T (n + 1) c → Dtot d c = 0 →
      (∀ s, k < s.card → c s = 0) → ∃ y, InTot T n y ∧ Dtot d y = c := by
    intro k
    induction k with
    | zero =>
      intro _ c hc _ h0
      refine ⟨0, ⟨rfl, fun q s _ => (T q s).zero_mem, fun _ _ => rfl⟩, ?_⟩
      funext s
      have hs : c s = 0 := by
        rcases Nat.eq_zero_or_pos s.card with h | h
        · rw [Finset.card_eq_zero.1 h]; exact hc.1
        · exact h0 s h
      simp [Dtot, delta, hs]
    | succ b ih =>
      intro hb c hc hD h0
      obtain ⟨q, hq⟩ : ∃ q, q + b = n := ⟨n - b, by omega⟩
      have hin : InCech (T q) (b + 1) (fun s => if s.card = b + 1 then c s else 0) := by
        refine ⟨by simp, fun s => ?_, fun s hs => by simp [hs]⟩
        by_cases hs : s.card = b + 1
        · simp only [hs, if_true]
          exact hc.2.1 q s (by omega)
        · simp only [hs, if_false]
          exact (T q s).zero_mem
      obtain ⟨y, hy, hyc⟩ := hC q b hq _ hin (delta_topPart_eq_zero d c (b + 1) hD h0)
      have hyT : InTot T n y := by
        refine ⟨hy.1, fun q' s hs => ?_, fun s hs => hy.2.2 s (by omega)⟩
        by_cases h : s.card = b
        · obtain rfl : q' = q := by omega
          exact hy.2.1 s
        · rw [hy.2.2 s h]; exact (T q' s).zero_mem
      have hDy : InTot T (n + 1) (Dtot d y) := (GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials d T hmono n y hyT).2 hdT
      have h1 : InTot T (n + 1) (c - Dtot d y) := by
        refine ⟨?_, fun q' s hs => (T q' s).sub_mem (hc.2.1 q' s hs) (hDy.2.1 q' s hs),
          fun s hs => ?_⟩
        · rw [Pi.sub_apply, hc.1, hDy.1, sub_zero]
        · rw [Pi.sub_apply, hc.2.2 s hs, hDy.2.2 s hs, sub_zero]
      have h2 : Dtot d (c - Dtot d y) = 0 := by rw [hsub, hD, hDD hdd, sub_zero]
      have h3 : ∀ s, b < s.card → (c - Dtot d y) s = 0 := by
        intro s hs
        have hys : y s = 0 := hy.2.2 s (by omega)
        by_cases h : s.card = b + 1
        · simp [Dtot, hyc, hys, h]
        · simp [Dtot, hyc, hys, h, h0 s (by omega)]
      obtain ⟨z, hz, hzc⟩ := ih (by omega) _ h1 h2 h3
      refine ⟨z + y, ⟨?_, fun q' s hs => (T q' s).add_mem (hz.2.1 q' s hs) (hyT.2.1 q' s hs),
        fun s hs => ?_⟩, ?_⟩
      · rw [Pi.add_apply, hz.1, hyT.1, add_zero]
      · rw [Pi.add_apply, hz.2.2 s hs, hyT.2.2 s hs, add_zero]
      · rw [hadd, hzc, sub_add_cancel]
  intro c hc hD
  exact key (n + 1) le_rfl c hc hD hc.2.2

end GlobalTheory.DI
