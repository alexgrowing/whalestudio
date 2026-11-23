import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

namespace GlobalTheory.SwapSlice

open GlobalTheory.WeilM

variable {k κ Y : Type}

def barL (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun Φ := fun y => starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y)
  map_add' Φ Ψ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((Φ + Ψ) x)) = (fun x => starRingEnd ℂ (Φ x)) + fun x => starRingEnd ℂ (Ψ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((Φ + Ψ) x)) y) = _
    rw [e, map_add, Pi.add_apply, map_add]
    rfl
  map_smul' c Φ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((c • Φ) x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (Φ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((c • Φ) x)) y) = _
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rfl

theorem barL_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ → k) → ℂ) (y : Y) :
    barL ι Φ y = starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y) := rfl

def sliceT (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] (Y × Y → ℂ) where
  toFun Φ := fun Z => barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2
  map_add' Φ Ψ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) =
        (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) + fun x₂ => ι (fun x₁ => Ψ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) = (fun x₁ => Φ (Sum.elim x₁ x₂)) + fun x₁ => Ψ (Sum.elim x₁ x₂) := rfl
      rw [e', map_add]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_add]
    rfl
  map_smul' c Φ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) =
        c • fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) = c • fun x₁ => Φ (Sum.elim x₁ x₂) := rfl
      rw [e', map_smul]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_smul]
    rfl

theorem sliceT_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ ⊕ κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι Φ Z = barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2 := rfl

def swapNeg [Neg Y] (Z : Y × Y) : Y × Y := (-Z.2, -Z.1)

theorem swapNeg_apply [Neg Y] (Z : Y × Y) : swapNeg Z = (-Z.2, -Z.1) := rfl

theorem sliceT_boxFun [CommRing k] (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ₁ φ₂ : (κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι (boxFun φ₁ φ₂) Z = ι φ₁ Z.1 * barL ι φ₂ Z.2 := by
  have e : (fun x₂ => ι (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) Z.1) = ι φ₁ Z.1 • φ₂ := by
    funext x₂
    have e' : (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [boxFun, Function.comp_def, mul_comm]
    rw [e', map_smul]
    simp [mul_comm]
  rw [sliceT_apply, e, map_smul]
  simp

end GlobalTheory.SwapSlice
