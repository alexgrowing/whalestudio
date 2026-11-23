import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Imports

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.twist :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a : ℤ_[l]), (l : ℤ_[l]) ∣ a - 1 →
      Unip g → Unip (a • g) := by
  intro l _ X _ _ g a ha hg
  obtain ⟨N, hN⟩ := hg
  obtain ⟨c, hc⟩ := ha
  have left : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (h * f) := by
    intro f h hf v
    obtain ⟨w, hw⟩ := hf v
    exact ⟨h w, by rw [Module.End.mul_apply, hw, map_smul]⟩
  have right : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (f * h) := by
    intro f h hf v
    exact hf (h v)
  have zero : InPow 1 (0 : Module.End ℤ_[l] X) := fun v => ⟨0, by simp⟩
  have add : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 h → InPow 1 (f + h) := by
    intro f h hf hh v
    obtain ⟨w, hw⟩ := hf v
    obtain ⟨u, hu⟩ := hh v
    exact ⟨w + u, by rw [LinearMap.add_apply, hw, hu, smul_add]⟩
  have hB : InPow 1 ((a - 1) • g) := by
    intro v
    refine ⟨c • g v, ?_⟩
    rw [LinearMap.smul_apply, hc, mul_smul, pow_one]
  have hcomm : Commute (g - 1) ((a - 1) • g) :=
    ((Commute.refl g).sub_left (Commute.one_left g)).smul_right (a - 1)
  have hsplit : a • g - 1 = (g - 1) + (a - 1) • g := by
    rw [sub_smul, one_smul]
    abel
  refine ⟨N, ?_⟩
  rw [hsplit, hcomm.add_pow]
  refine Finset.sum_induction _ (InPow 1) add zero ?_
  intro m hm
  rcases Nat.lt_or_ge m N with hlt | hge
  · obtain ⟨k, hk⟩ : ∃ k, N - m = k + 1 := ⟨N - m - 1, by omega⟩
    rw [hk, pow_succ']
    apply right
    rw [← mul_assoc]
    apply right
    exact left _ _ hB
  · have hmN : m = N := by
      simp only [Finset.mem_range] at hm
      omega
    subst hmN
    exact right _ _ (right _ _ hN)
