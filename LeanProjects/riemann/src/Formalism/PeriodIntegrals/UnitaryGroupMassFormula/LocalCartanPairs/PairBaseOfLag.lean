import Mathlib
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique

noncomputable section

namespace PI.LocCartanPair

open Matrix IsLocalRing

section Lag

variable {R : Type} [CommRing R] [StarRing R]

theorem lag_congr {ι : Type} [Fintype ι] [DecidableEq ι] (A B P e : Matrix ι ι R)
    (hP : IsUnit P.det) (hPAB : Pᴴ * A * P = B) (he : e * e = e)
    (heB : eᴴ * B = B * (1 - e)) :
    (P * e * P⁻¹) * (P * e * P⁻¹) = P * e * P⁻¹ ∧
      (P * e * P⁻¹)ᴴ * A = A * (1 - P * e * P⁻¹) := by
  have h1 : P⁻¹ * P = 1 := nonsing_inv_mul P hP
  have h2 : P * P⁻¹ = 1 := mul_nonsing_inv P hP
  have hPX : ∀ X : Matrix ι ι R, P⁻¹ * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have h4 : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hQX : ∀ X : Matrix ι ι R, Pᴴ * ((P⁻¹)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  have hA : A = (P⁻¹)ᴴ * B * P⁻¹ := by
    rw [← hPAB]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  constructor
  · simp only [Matrix.mul_assoc, hPX]
    rw [← Matrix.mul_assoc e e, he]
  · calc (P * e * P⁻¹)ᴴ * A = (P⁻¹)ᴴ * (eᴴ * B) * P⁻¹ := by
          rw [hA]
          simp only [conjTranspose_mul, Matrix.mul_assoc, hQX]
      _ = (P⁻¹)ᴴ * (B * (1 - e)) * P⁻¹ := by rw [heB]
      _ = A * (1 - P * e * P⁻¹) := by
          rw [hA]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, hPX]

theorem lag_reindex {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (s : β ≃ ι) (A : Matrix ι ι R) (E : Matrix β β R) (hE : E * E = E)
    (hEA : Eᴴ * A.submatrix s s = A.submatrix s s * (1 - E)) :
    E.submatrix s.symm s.symm * E.submatrix s.symm s.symm = E.submatrix s.symm s.symm ∧
      (E.submatrix s.symm s.symm)ᴴ * A = A * (1 - E.submatrix s.symm s.symm) := by
  have hA : A = (A.submatrix s s).submatrix s.symm s.symm := by simp
  constructor
  · rw [submatrix_mul_equiv, hE]
  · have h1 : (1 : Matrix ι ι R) - E.submatrix s.symm s.symm = (1 - E).submatrix s.symm s.symm := by
      ext i j
      simp [Matrix.one_apply]
    rw [h1, conjTranspose_submatrix]
    conv_lhs => rw [hA]
    conv_rhs => rw [hA]
    rw [submatrix_mul_equiv, submatrix_mul_equiv, hEA]

variable (κ : Type) [Fintype κ] [DecidableEq κ]

def hypJ : Matrix (κ ⊕ κ) (κ ⊕ κ) R := fromBlocks 0 1 1 0

def hypE : Matrix (κ ⊕ κ) (κ ⊕ κ) R := fromBlocks 1 0 0 0

theorem hypJ_herm : (hypJ κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R)ᴴ = hypJ κ := by
  simp [hypJ, fromBlocks_conjTranspose]

theorem hypJ_sq : (hypJ κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R) * hypJ κ = 1 := by
  simp [hypJ, fromBlocks_multiply]

theorem hypJ_det : IsUnit (hypJ κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R).det := by
  refine IsUnit.of_mul_eq_one (hypJ κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R).det ?_
  rw [← det_mul, hypJ_sq, det_one]

theorem hypE_idem : (hypE κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R) * hypE κ = hypE κ := by
  simp [hypE, fromBlocks_multiply]

theorem hypE_lag : (hypE κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R)ᴴ * hypJ κ = hypJ κ * (1 - hypE κ) := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) - hypE κ = fromBlocks 0 0 0 1 := by
    rw [← fromBlocks_one, hypE, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp
  rw [h1]
  simp [hypE, hypJ, fromBlocks_conjTranspose, fromBlocks_multiply]

end Lag

section Main

variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
  [HenselianLocalRing R₀] [Finite (ResidueField R₀)]

theorem lag_exists_sum (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (hA : Aᴴ = A)
    (hdet : IsUnit A.det) :
    ∃ e : Matrix (κ ⊕ κ) (κ ⊕ κ) R, e * e = e ∧ eᴴ * A = A * (1 - e) := by
  obtain ⟨g, hg, hgA⟩ := Formalism.HermitianLatticesTheory.unimodUnramUnique_main hR₀ hθ _ (κ ⊕ κ) rfl A hA hdet
  obtain ⟨c, hc, hcJ⟩ := Formalism.HermitianLatticesTheory.unimodUnramUnique_main hR₀ hθ _ (κ ⊕ κ) rfl
    (hypJ κ) (hypJ_herm κ) (hypJ_det κ)
  have hc1 : c * c⁻¹ = 1 := mul_nonsing_inv c hc
  have hc2 : (c⁻¹)ᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, hc1, conjTranspose_one]
  have hcX : ∀ X : Matrix (κ ⊕ κ) (κ ⊕ κ) R, (c⁻¹)ᴴ * (cᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hc2, Matrix.one_mul]
  have hP : IsUnit (g * c⁻¹).det := by
    rw [det_mul]; exact hg.mul (isUnit_nonsing_inv_det c hc)
  have hPA : (g * c⁻¹)ᴴ * A * (g * c⁻¹) = hypJ κ := by
    calc (g * c⁻¹)ᴴ * A * (g * c⁻¹) = (c⁻¹)ᴴ * (gᴴ * A * g) * c⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (c⁻¹)ᴴ * (cᴴ * hypJ κ * c) * c⁻¹ := by rw [hgA, hcJ]
      _ = hypJ κ := by simp only [Matrix.mul_assoc, hc1, Matrix.mul_one, hcX]
  exact ⟨_, lag_congr A (hypJ κ) (g * c⁻¹) (hypE κ) hP hPA (hypE_idem κ) (hypE_lag κ)⟩

theorem lag_exists (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Even (Fintype.card ι)) (A : Matrix ι ι R)
    (hA : Aᴴ = A) (hdet : IsUnit A.det) :
    ∃ e : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) := by
  obtain ⟨m, hm⟩ := hι
  let s : Fin m ⊕ Fin m ≃ ι := Fintype.equivOfCardEq (by simp [hm])
  have hB : (A.submatrix s s)ᴴ = A.submatrix s s := by rw [conjTranspose_submatrix, hA]
  have hBdet : IsUnit (A.submatrix s s).det := by rw [det_submatrix_equiv_self]; exact hdet
  obtain ⟨E, hE, hEA⟩ := lag_exists_sum hR₀ hθ (Fin m) _ hB hBdet
  exact ⟨_, lag_reindex s A E hE hEA⟩

theorem pair_base_of_lag {ι : Type} [Fintype ι] [DecidableEq ι] (A e h h₁ : Matrix ι ι R) (c : R)
    (hh : h = c • h₁) (hh₁ : IsUnit h₁.det) (he : e * e = e) (heA : eᴴ * A = A * (1 - e)) :
    ∃ e f : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) ∧ e * h = h * f := by
  refine ⟨e, h₁⁻¹ * e * h₁, he, heA, ?_⟩
  rw [hh, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_nonsing_inv h₁ hh₁, Matrix.one_mul]

theorem pair_base (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Even (Fintype.card ι)) (A : Matrix ι ι R)
    (hA : Aᴴ = A) (hdet : IsUnit A.det) (h h₁ : Matrix ι ι R) (c : R)
    (hh : h = c • h₁) (hh₁ : IsUnit h₁.det) :
    ∃ e f : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) ∧ e * h = h * f := by
  obtain ⟨e, he, heA⟩ := lag_exists hR₀ hθ hι A hA hdet
  exact pair_base_of_lag A e h h₁ c hh hh₁ he heA

end Main

end PI.LocCartanPair
