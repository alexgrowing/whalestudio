import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.CWCombo

theorem isCWCont_of_sobCont {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hs : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → SmoothVec (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ v)
    {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {ι : Type} [Fintype ι] (l : ι → H →ₗ[ℂ] ℂ) (b : ι → Wp)
    (hl : ∀ i, Sobolev₂ (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ (l i)) {B : H → Wp}
    (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = ∑ i, l i v • b i) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  classical
  have hnn : ∀ (L : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))) (v : H),
      0 ≤ (L.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := fun L v =>
    List.sum_nonneg (by
      intro x hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _)
  have key : ∀ s : Finset ι, ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, ∀ X ∈ w, PI.UpqRep.InLieHpk k r X) ∧
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ‖∑ i ∈ s, l i v • b i‖ ≤
        C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, [], by simp, by simp⟩
    | insert i s hi ih =>
      obtain ⟨C, Ws, hW, hb⟩ := ih
      obtain ⟨S, D, hS, hD⟩ := hl i
      refine ⟨|D| * ‖b i‖ + |C|, S ++ Ws, ?_, ?_⟩
      · intro w hw X hX
        rcases List.mem_append.1 hw with h | h
        · exact hS w h X hX
        · exact hW w h X hX
      · intro v hv
        have e : ‖l i v‖ ≤ D * (S.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := by
          have := hD v (hs v hv)
          simpa only [dsigW_eq] using this
        have h1 := hnn S v
        have h2 := hnn Ws v
        have h3 := hb v hv
        rw [Finset.sum_insert hi, List.map_append, List.sum_append]
        set P := (S.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum
        set Q := (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum
        have hbn : 0 ≤ ‖b i‖ := norm_nonneg _
        have e1 : ‖l i v • b i‖ ≤ |D| * ‖b i‖ * P := by
          rw [norm_smul]
          calc ‖l i v‖ * ‖b i‖ ≤ (|D| * P) * ‖b i‖ :=
                mul_le_mul_of_nonneg_right (e.trans (mul_le_mul_of_nonneg_right (le_abs_self D) h1)) hbn
            _ = |D| * ‖b i‖ * P := by ring
        have e2 : ‖∑ j ∈ s, l j v • b j‖ ≤ |C| * Q :=
          h3.trans (mul_le_mul_of_nonneg_right (le_abs_self C) h2)
        have a1 : 0 ≤ |D| * ‖b i‖ * Q := mul_nonneg (mul_nonneg (abs_nonneg _) hbn) h2
        have a2 : 0 ≤ |C| * P := mul_nonneg (abs_nonneg _) h1
        calc ‖l i v • b i + ∑ j ∈ s, l j v • b j‖ ≤ ‖l i v • b i‖ + ‖∑ j ∈ s, l j v • b j‖ := norm_add_le _ _
          _ ≤ |D| * ‖b i‖ * P + |C| * Q := add_le_add e1 e2
          _ ≤ (|D| * ‖b i‖ + |C|) * (P + Q) := by nlinarith
  obtain ⟨C, Ws, hW, hb⟩ := key Finset.univ
  exact ⟨C, Ws, hW, fun v hv => by rw [hB v hv]; exact hb v hv⟩

end UpperTheory.Lit.Bur.CWCombo

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.casselmanWallachCont_finite_sum_sobolev_forms : ∀ {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hs : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → SmoothVec (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ v) {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {ι : Type} [Fintype ι] (l : ι → H →ₗ[ℂ] ℂ) (b : ι → Wp) (hl : ∀ i, Sobolev₂ (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ (l i)) {B : H → Wp} (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = ∑ i, l i v • b i), PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  first | exact @UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont | exact UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont | (intros; apply UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont <;> assumption)
