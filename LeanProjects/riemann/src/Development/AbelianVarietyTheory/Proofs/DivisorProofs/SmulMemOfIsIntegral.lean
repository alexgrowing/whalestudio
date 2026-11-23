import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def endLat (Λ : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {Y | ∀ x ∈ Λ, Y *ᵥ x ∈ Λ}
  zero_mem' x _ := by simp
  add_mem' {Y Z} hY hZ x hx := by rw [add_mulVec]; exact Λ.add_mem (hY x hx) (hZ x hx)
  neg_mem' {Y} hY x hx := by rw [neg_mulVec]; exact Λ.neg_mem (hY x hx)

theorem mem_endLat {Λ : Submodule (𝓞 E) (Fin r → E)} {Y : Matrix (Fin r) (Fin r) E} :
    Y ∈ endLat Λ ↔ ∀ x ∈ Λ, Y *ᵥ x ∈ Λ := Iff.rfl

def IsSkew (G Y : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0

def skewLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {Y | IsSkew G Y ∧ Y ∈ endLat Λ}
  zero_mem' := ⟨fun u w => by simp [herm, cc], (endLat Λ).zero_mem⟩
  add_mem' {Y Z} hY hZ := by
    refine ⟨fun u w => ?_, (endLat Λ).add_mem hY.2 hZ.2⟩
    have h1 := hY.1 u w
    have h2 := hZ.1 u w
    simp only [herm, cc, add_mulVec, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  neg_mem' {Y} hY := by
    refine ⟨fun u w => ?_, (endLat Λ).neg_mem hY.2⟩
    have h1 := hY.1 u w
    simp only [herm, cc, neg_mulVec, Pi.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib] at h1 ⊢
    linear_combination -h1

def hAdj (G Y : Matrix (Fin r) (Fin r) E) : Matrix (Fin r) (Fin r) E := (G⁻¹ * Yᵀ * G).map cc

def imLat (E : Type) [Field E] [NumberField E] [IsCMField E] : AddSubgroup E where
  carrier := {a | IsIntegral ℤ a ∧ cc a = -a}
  zero_mem' := ⟨isIntegral_zero, by simp [cc]⟩
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, by simp only [cc, map_add] at ha hb ⊢; rw [ha.2, hb.2, neg_add]⟩
  neg_mem' {a} ha := ⟨ha.1.neg, by simp only [cc, map_neg] at ha ⊢; rw [ha.2]⟩

def trProj (Y : Matrix (Fin r) (Fin r) E) : Matrix (Fin r) (Fin r) E :=
  Y - (Y.trace / r) • (1 : Matrix (Fin r) (Fin r) E)

def dualLie (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {Y | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧
    ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}
  zero_mem' := ⟨by simp, fun u w => by simp [herm, cc], fun X _ => by simpa using isIntegral_zero⟩
  add_mem' {Y Z} hY hZ := by
    refine ⟨by rw [trace_add, hY.1, hZ.1, add_zero], fun u w => ?_, fun X hX => ?_⟩
    · have h1 := hY.2.1 u w
      have h2 := hZ.2.1 u w
      simp only [herm, cc, add_mulVec, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
      linear_combination h1 + h2
    · rw [Matrix.mul_add, trace_add]; exact (hY.2.2 X hX).add (hZ.2.2 X hX)
  neg_mem' {Y} hY := by
    refine ⟨by rw [trace_neg, hY.1, neg_zero], fun u w => ?_, fun X hX => ?_⟩
    · have h1 := hY.2.1 u w
      simp only [herm, cc, neg_mulVec, Pi.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib] at h1 ⊢
      linear_combination -h1
    · rw [Matrix.mul_neg, trace_neg]; exact (hY.2.2 X hX).neg

theorem closure_dualLie (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧
      ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))} = dualLie G Λ :=
  AddSubgroup.closure_eq (dualLie G Λ)

theorem cc_cc (a : E) : cc (cc a) = a := by simp [cc]

theorem smul_mem_of_isIntegral {Λ : Submodule (𝓞 E) (Fin r → E)} {c : E} (hc : IsIntegral ℤ c)
    {x : Fin r → E} (hx : x ∈ Λ) : c • x ∈ Λ := by
  have h := Λ.smul_mem (⟨c, hc⟩ : 𝓞 E) hx
  convert h using 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
  rfl

theorem smul_mem_endLat {Λ : Submodule (𝓞 E) (Fin r → E)} {c : E} (hc : IsIntegral ℤ c)
    {Y : Matrix (Fin r) (Fin r) E} (hY : Y ∈ endLat Λ) : c • Y ∈ endLat Λ := fun x hx => by
  have : (c • Y) *ᵥ x = c • (Y *ᵥ x) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this]; exact smul_mem_of_isIntegral hc (hY x hx)

theorem mul_mem_endLat {Λ : Submodule (𝓞 E) (Fin r → E)} {Y Z : Matrix (Fin r) (Fin r) E}
    (hY : Y ∈ endLat Λ) (hZ : Z ∈ endLat Λ) : Y * Z ∈ endLat Λ := fun x hx => by
  rw [← mulVec_mulVec]; exact hY _ (hZ x hx)

theorem one_mem_endLat {Λ : Submodule (𝓞 E) (Fin r → E)} : (1 : Matrix (Fin r) (Fin r) E) ∈ endLat Λ :=
  fun x hx => by rw [one_mulVec]; exact hx

end GlobalTheory.LieDisc
