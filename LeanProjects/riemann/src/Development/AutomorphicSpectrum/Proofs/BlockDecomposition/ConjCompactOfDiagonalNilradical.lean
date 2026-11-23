import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan.Slice

def dg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (Matrix.diag M)

theorem continuous_dg {n : ℕ} : Continuous (dg (n := n)) :=
  continuous_id.matrix_diag.matrix_diagonal

theorem dg_one_add_mul {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (hZ : ∀ i, Z i i = 0) : dg ((1 + Z) * Matrix.diagonal a) = Matrix.diagonal a := by
  unfold dg
  congr 1
  funext i
  simp [Matrix.diag_apply, Matrix.mul_diagonal, hZ]

theorem dg_mul_one_add {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (hZ : ∀ i, Z i i = 0) : dg (Matrix.diagonal a * (1 + Z)) = Matrix.diagonal a := by
  unfold dg
  congr 1
  funext i
  simp [Matrix.diag_apply, Matrix.diagonal_mul, hZ]

theorem isCompact_units {n : ℕ} {B₁ B₂ : Set (Matrix (Fin n) (Fin n) ℂ)}
    (h₁ : IsCompact B₁) (h₂ : IsCompact B₂) :
    IsCompact {u : GL (Fin n) ℂ | u.val ∈ B₁ ∧ (u⁻¹ : GL (Fin n) ℂ).val ∈ B₂} := by
  have h := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) ℂ)).isCompact_preimage
      (h₁.prod (h₂.image MulOpposite.continuous_op))
  convert h using 1
  ext u
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, ⟨_, h', rfl⟩⟩
  · rintro ⟨h, ⟨x, hx, e⟩⟩
    have e' : x = (u⁻¹ : GL (Fin n) ℂ).val := MulOpposite.op_injective e
    exact ⟨h, e' ▸ hx⟩

theorem conj_uOf_val {n : ℕ} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (P : GL (Fin n) ℂ)
    (X : nilrad W₁ W₂) :
    (P⁻¹ * uOf X * P).val = 1 + (P⁻¹ : GL (Fin n) ℂ).val * X.1 * P.val := by
  have h1 : (P⁻¹ : GL (Fin n) ℂ).val * P.val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem slice_measure_ne_top : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
  (P : GL (Fin n) ℂ), W₁ ≤ W₂ →
  (∀ t ∈ twCent (thC n) d, ∃ a : Fin n → ℂ, (P⁻¹ * t * P).val = Matrix.diagonal a) →
  (∀ X ∈ nilrad W₁ W₂, ∀ i, ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i = 0) →
  ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤ := by
  intro n _ _ d μd _ W₁ W₂ P hW hdiag hzero C hC g
  let D₁ : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun c => dg (P⁻¹ * (c * g⁻¹) * P).val
  let D₂ : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun c => dg (P⁻¹ * (g * c⁻¹) * P).val
  have hD₁ : Continuous D₁ := continuous_dg.comp
    (Units.continuous_val.comp ((continuous_const.mul (continuous_id.mul continuous_const)).mul
      continuous_const))
  have hD₂ : Continuous D₂ := continuous_dg.comp
    (Units.continuous_val.comp ((continuous_const.mul (continuous_const.mul continuous_inv)).mul
      continuous_const))
  have hK := isCompact_units (hC.image hD₁) (hC.image hD₂)
  have hK' := hK.image (f := fun u : GL (Fin n) ℂ => P * u * P⁻¹)
    ((continuous_const.mul continuous_id).mul continuous_const)
  have hKT := (isClosed_twCent d).isClosedEmbedding_subtypeVal.isCompact_preimage hK'
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) hKT.measure_lt_top)
  rintro ⟨t, ht⟩ ⟨X, c, hc, hX⟩
  change uOf X * c = t * g at hX
  obtain ⟨a, ha⟩ := hdiag t ht
  obtain ⟨b, hb⟩ := hdiag t⁻¹ ((twCent (thC n) d).inv_mem ht)
  have hcX : c = (uOf X)⁻¹ * (t * g) := eq_inv_mul_of_mul_eq hX
  have e₁ : P⁻¹ * (c * g⁻¹) * P = (P⁻¹ * uOf (ninv hW X) * P) * (P⁻¹ * t * P) := by
    rw [uOf_ninv, hcX]; group
  have e₂ : P⁻¹ * (g * c⁻¹) * P = (P⁻¹ * t⁻¹ * P) * (P⁻¹ * uOf X * P) := by
    rw [hcX]; group
  have e₃ : (P⁻¹ * t * P)⁻¹ = P⁻¹ * t⁻¹ * P := by group
  refine ⟨P⁻¹ * t * P, ⟨⟨c, hc, ?_⟩, ⟨c, hc, ?_⟩⟩, by group⟩
  · change dg (P⁻¹ * (c * g⁻¹) * P).val = _
    rw [e₁, Units.val_mul, conj_uOf_val, ha]
    exact dg_one_add_mul _ _ (hzero _ (ninv hW X).2)
  · change dg (P⁻¹ * (g * c⁻¹) * P).val = _
    rw [e₂, e₃, Units.val_mul, conj_uOf_val, hb]
    exact dg_mul_one_add _ _ (hzero _ X.2)

end GlobalTheory.CompanionTheory.LocVan.Slice
end
