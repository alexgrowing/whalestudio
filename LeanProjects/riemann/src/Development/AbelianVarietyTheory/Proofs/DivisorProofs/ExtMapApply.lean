import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv

set_option autoImplicit false

noncomputable section

open Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TorsionForm

def genProd {m : ℕ} (φ : Matrix (Fin m) (Fin m) ℂ) (S : Finset (Fin m)) : Ext m :=
  (S.sort (· ≤ ·)).foldr (fun i acc => ∑ k, φ i k • wedge k acc) (Pi.single ∅ 1)

def extMap {m : ℕ} (φ : Matrix (Fin m) (Fin m) ℂ) : Ext m →L[ℂ] Ext m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => ∑ S, w S • genProd φ S
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c w => by simp [Finset.smul_sum, smul_smul] }

theorem extMap_apply {m : ℕ} (φ : Matrix (Fin m) (Fin m) ℂ) (w : Ext m) :
    extMap φ w = ∑ S, w S • genProd φ S := rfl

def fibMat (n : ℕ) {g : ℕ} (a : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin (n + n + g)) (Fin (n + n + g)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 a)

theorem fibMat_mul (n : ℕ) {g : ℕ} (a a' : Matrix (Fin g) (Fin g) ℂ) :
    fibMat n a * fibMat n a' = fibMat n (a * a') := by
  simp [fibMat, Matrix.fromBlocks_multiply]

theorem fibMat_one (n g : ℕ) : fibMat n (1 : Matrix (Fin g) (Fin g) ℂ) = 1 := by
  simp [fibMat, Matrix.fromBlocks_one]

def frameMap (n : ℕ) {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) : Ext (n + n + g) →L[ℂ] Ext (n + n + g) :=
  extMap (fibMat n (D⁻¹)ᴴ)

def frameMapInv (n : ℕ) {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) :
    Ext (n + n + g) →L[ℂ] Ext (n + n + g) :=
  extMap (fibMat n Dᴴ)

def kerConj (n : ℕ) {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ)
    (K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (n + n + g) →L[ℂ] Ext (n + n + g)) :
    ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (n + n + g) →L[ℂ] Ext (n + n + g) :=
  fun t z z' => frameMap n D ∘L K t (z ᵥ* D⁻¹) (z' ᵥ* D⁻¹) ∘L frameMapInv n D

end GlobalTheory.TorsionForm
