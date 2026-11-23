import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
open MeasureTheory GlobalTheory.Chamber

namespace GlobalTheory.Chamber.SumSplit

open Finset in
theorem empty_mem_parF {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) : (∅ : Finset (SV k)) ∈ parF 𝔞 ∅ := by
  refine mem_parF.2 ⟨⟨by simp, by simp⟩, ?_, subset_rfl⟩
  simp [aP]

theorem eL_zero {k : ℕ} (H : A0 k) : eL 0 H = 1 := by simp [eL]

theorem eL_add {k : ℕ} (l H H' : A0 k) : eL l (H + H') = eL l H * eL l H' := by
  simp only [eL, inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem sum_isOrth {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {X Y W : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X)
    (hY : IsOrth 𝔞 Y) (hW : ∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) : IsOrth 𝔞 W := by
  intro P hP Q e
  have hQ : Q ∈ parF 𝔞 ∅ := mem_parF.2 ⟨(mem_parF.1 hP).1.mono e, (vecSpan_mono e).trans (mem_parF.1 hP).2.1,
    Finset.empty_subset _⟩
  rw [hW P hP, hW Q hQ, map_add, ← hX P hP Q e, ← hY P hP Q e]

theorem cP_empty_empty {k : ℕ} (c : Finset (SV k) → A0 k → ℂ) (hc : Continuous (c ∅)) (l : A0 k) :
    cP ∅ ∅ c l = c ∅ l := by
  have hs : sumP ∅ ∅ c = c ∅ := by
    funext l
    have h : ∀ b : SV k → A0 k, epsOf (∅ \ ∅) b l = 1 := fun b => by
      have : IsEmpty ↥((∅ : Finset (SV k)) \ ∅) := ⟨fun x => by simpa using x.2⟩
      rw [epsOf, Matrix.det_isEmpty]; simp
    simp only [sumP, between, Finset.powerset_empty, Finset.filter_singleton, Finset.Subset.refl, if_true,
      Finset.sum_singleton, eps, epsHat, h]
    simp
  rw [cP, hs]
  refine extendFrom_eq (by rw [dense_generic.closure_eq]; trivial) ?_
  exact (hc.tendsto l).mono_left nhdsWithin_le_nhds

theorem volume_sum_split : ExpFamilyIntegral → FamilyProduct → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 →
    ∀ X Y W : Finset (SV k) → A0 k, IsOrth 𝔞 X → IsOrth 𝔞 Y → (∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) →
    ((∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ W H : ℝ) : ℂ) = cM 𝔞 ∅ (expFam W) 0 ∧
    cM 𝔞 ∅ (expFam W) 0 = ∑ Q ∈ parF 𝔞 ∅, cM 𝔞 Q (expFam X) 0 * cP Q ∅ (expFam Y) 0 ∧
    cP ∅ ∅ (expFam Y) 0 = 1 := by
  intro hI hF k 𝔞 hL X Y W hX hY hW
  have hWo := sum_isOrth hX hY hW
  refine ⟨?_, ?_, ?_⟩
  · rw [(((hI k 𝔞 hL W hWo).2 ∅ (empty_mem_parF 𝔞)).1.2 0)]
    simp only [eL_zero, one_mul]
    exact (integral_ofReal).symm
  · rw [← hF k 𝔞 hL _ _ hX.isGMFam hY.isGMFam ∅ (empty_mem_parF 𝔞) 0]
    have hs : sumM 𝔞 ∅ (expFam W) = sumM 𝔞 ∅ (expFam X * expFam Y) := by
      funext l
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPF : P ∈ parF 𝔞 ∅ := mem_parF.2 ⟨(mem_parP.1 hP).1, (mem_parP.1 hP).2.1.le, Finset.empty_subset _⟩
      simp only [expFam, Pi.mul_apply, hW P hPF, eL_add]
    simp only [cM, hs]
  · rw [cP_empty_empty _ (by
      simpa [expFam] using (((hY.isGMFam) ∅ (empty_mem_parF 𝔞)).1.continuous)) 0]
    exact eL_zero _

end GlobalTheory.Chamber.SumSplit
