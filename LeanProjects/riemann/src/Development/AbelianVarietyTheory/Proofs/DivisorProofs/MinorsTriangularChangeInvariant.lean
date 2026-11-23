import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulUpperTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat.CramerFrame

theorem minorAt_triChange {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K)
    (Tm : Matrix (Fin g) (Fin g) K) (hT : Tm.BlockTriangular id) (hd : ∀ i, Tm i i ≠ 0)
    (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)) :
    minorAt H k hk τ = minorAt (H * Tm⁻¹) k hk τ * ∏ i : Fin k, Tm (Fin.castLE hk i) (Fin.castLE hk i) := by
  have hdet : IsUnit Tm.det := by
    rw [Matrix.det_of_upperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have hH : H * Tm⁻¹ * Tm = H := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Tm hdet, Matrix.mul_one]
  conv_lhs => rw [← hH]
  exact minorAt_mul_upperTriangular (H * Tm⁻¹) Tm hT k hk τ

theorem prod_diag_ne_zero {K : Type} [Field K] {g : ℕ} (Tm : Matrix (Fin g) (Fin g) K) (hd : ∀ i, Tm i i ≠ 0)
    (k : ℕ) (hk : k ≤ g) : (∏ i : Fin k, Tm (Fin.castLE hk i) (Fin.castLE hk i)) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => hd _

theorem prod_diag_succ {K : Type} [Field K] {g : ℕ} (Tm : Matrix (Fin g) (Fin g) K) (i : Fin g) :
    (∏ j : Fin ((i : ℕ) + 1), Tm (Fin.castLE i.2 j) (Fin.castLE i.2 j)) =
      (∏ j : Fin (i : ℕ), Tm (Fin.castLE i.2.le j) (Fin.castLE i.2.le j)) * Tm i i := by
  rw [Fin.prod_univ_castSucc]
  have h1 : Fin.castLE i.2 (Fin.last (i : ℕ)) = i := Fin.ext (by simp)
  have h2 : ∀ j : Fin (i : ℕ), Fin.castLE i.2 (Fin.castSucc j) = Fin.castLE i.2.le j := fun j => Fin.ext (by simp)
  simp only [h1, h2]

theorem triChange {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K)
    (Tm : Matrix (Fin g) (Fin g) K) : Tm.BlockTriangular id → (∀ i, Tm i i ≠ 0) →
    ∀ (σ : ∀ k : ℕ, Fin k → Fin (g + g)),
      (∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)),
        minorAt H k hk τ = minorAt (H * Tm⁻¹) k hk τ * ∏ i : Fin k, Tm (Fin.castLE hk i) (Fin.castLE hk i)) ∧
      cramerCol H σ = cramerCol (H * Tm⁻¹) σ ∧
      ((∀ (k : ℕ) (hk : k ≤ g), minorAt (H * Tm⁻¹) k hk (σ k) ≠ 0) → ∀ i : Fin g,
        (frameC H σ i : K) = Tm i i * minorAt (H * Tm⁻¹) ((i : ℕ) + 1) i.2 (σ ((i : ℕ) + 1)) /
          minorAt (H * Tm⁻¹) i i.2.le (σ i)) := by
  intro hT hd σ
  have h1 := minorAt_triChange H Tm hT hd
  refine ⟨h1, ?_, ?_⟩
  · ext r k
    simp only [cramerCol, Matrix.of_apply]
    rw [h1, h1]
    exact mul_div_mul_right _ _ (prod_diag_ne_zero Tm hd _ _)
  · intro hne i
    have hA := hne ((i : ℕ) + 1) i.2
    have hB := hne (i : ℕ) i.2.le
    have hP1 := prod_diag_ne_zero Tm hd ((i : ℕ) + 1) i.2
    have hP0 := prod_diag_ne_zero Tm hd (i : ℕ) i.2.le
    rw [frameC_val H σ i (by rw [h1]; exact mul_ne_zero hA hP1) (by rw [h1]; exact mul_ne_zero hB hP0), h1, h1,
      prod_diag_succ]
    field_simp

end GlobalTheory.ConstLat.CramerFrame

end
