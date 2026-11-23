import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpreadStatement

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem spread_le_at {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hW : W.Hyp) (hD : W.IsDiv) (τ : ι)
    (j : ℕ) (hj : j ≤ N - W.kc) :
    (j : ℝ) * ((⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i) ≤ 6 * ∑ i, |(W.u' τ i : ℝ)| := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.T.dividedWeight_nodes_far_and_spread ι N W hW hD τ
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hW.p_lt
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := reWt W.u' τ)
  obtain ⟨b, hb⟩ := exists_eq_ciInf_of_finite (f := reWt W.u' τ)
  have hsp : (⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i ≤ 3 / 2 * W.w τ / W.T := by
    rw [← ha, ← hb]; exact h2 a b
  have h0 : 0 ≤ 3 / 2 * W.w τ / W.T := by simpa using h2 a a
  have hkN : W.kc < N := hW.kc_lt.trans hW.p_lt
  set s : Finset (Fin N) := Finset.Ici (⟨W.kc, hkN⟩ : Fin N) with hs
  have hcard : s.card = N - W.kc := by simp [hs]
  have hsum : (s.card : ℝ) * (W.w τ / (4 * W.T)) ≤ ∑ i ∈ s, |(W.u' τ i : ℝ)| := by
    have := Finset.card_nsmul_le_sum s (fun i => |(W.u' τ i : ℝ)|) (W.w τ / (4 * W.T))
      (fun i hi => (h1 i (by simpa [hs, Fin.le_def] using hi)).2)
    simpa [nsmul_eq_mul] using this
  have hsub : ∑ i ∈ s, |(W.u' τ i : ℝ)| ≤ ∑ i, |(W.u' τ i : ℝ)| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
  have hjc : (j : ℝ) ≤ s.card := by rw [hcard]; exact_mod_cast hj
  have he : 3 / 2 * W.w τ / W.T = 6 * (W.w τ / (4 * W.T)) := by ring
  calc (j : ℝ) * ((⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i) ≤ j * (3 / 2 * W.w τ / W.T) :=
        mul_le_mul_of_nonneg_left hsp (Nat.cast_nonneg _)
    _ ≤ s.card * (3 / 2 * W.w τ / W.T) := mul_le_mul_of_nonneg_right hjc h0
    _ = 6 * (s.card * (W.w τ / (4 * W.T))) := by rw [he]; ring
    _ ≤ _ := by linarith

end GlobalTheory.MeanTop
