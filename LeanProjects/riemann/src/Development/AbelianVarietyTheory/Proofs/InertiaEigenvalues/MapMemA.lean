import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec

noncomputable section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.LiftCoker

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem map_mem_A (f : O⟦X⟧) : PowerSeries.map (algebraMap O K) f ∈ A O K := by
  rw [← coe_equivA]
  exact (equivA O K f).2

variable (O K) in

def colon {ι κ : Type} [Fintype ι] (G : Matrix κ ι K⟦X⟧) : Ideal O⟦X⟧ where
  carrier := {α | ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) →
    ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧ PowerSeries.map (algebraMap O K) α • w = G *ᵥ m}
  add_mem' {α β} hα hβ w hw := by
    obtain ⟨m, hm, h⟩ := hα w hw
    obtain ⟨m', hm', h'⟩ := hβ w hw
    exact ⟨m + m', fun j => add_mem (hm j) (hm' j), by rw [map_add, add_smul, h, h', Matrix.mulVec_add]⟩
  zero_mem' w _ := ⟨0, fun _ => zero_mem _, by simp⟩
  smul_mem' c α hα w hw := by
    obtain ⟨m, hm, h⟩ := hα w hw
    refine ⟨PowerSeries.map (algebraMap O K) c • m, fun j => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (map_mem_A c) (hm j)
    · rw [smul_eq_mul, map_mul, mul_smul, h, Matrix.mulVec_smul]

theorem mem_colon {ι κ : Type} [Fintype ι] {G : Matrix κ ι K⟦X⟧} {α : O⟦X⟧} :
    α ∈ colon O K G ↔ ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) →
      ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧ PowerSeries.map (algebraMap O K) α • w = G *ᵥ m := Iff.rfl

end GlobalTheory.LiftCoker
