import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianRepresentationsResidueStatement

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem red_cT_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) :
    red ϖ 1 (cT σ x) = cT (barσ σ ϖ h 1) (red ϖ 1 x) := by
  ext i j
  simp only [red, cT, Matrix.map_apply, Matrix.transpose_apply, barσ_mk]

theorem red_mul_one {R : Type} [CommRing R] (ϖ : R) {a b c : ℕ}
    (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ 1 (x * y) = red ϖ 1 x * red ϖ 1 y := by
  simp only [red]
  exact Matrix.map_mul

theorem red_surj_one {R : Type} [CommRing R] (ϖ : R) {a b : ℕ}
    (y : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ 1)) : ∃ x, red ϖ 1 x = y := by
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  simp only [red, Matrix.map_apply, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec

theorem isUnit_det_red_one {R : Type} [CommRing R] (ϖ : R) {a : ℕ}
    (x : Matrix (Fin a) (Fin a) R) (hx : IsUnit x.det) : IsUnit (red ϖ 1 x).det := by
  have e : (red ϖ 1 x).det = Ideal.Quotient.mk (lev ϖ 1) x.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact hx.map _

theorem red_image_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ 1 '' {x : Matrix (Fin m) (Fin n) R | red ϖ 1 (cT σ x * S * x) = red ϖ 1 T} =
      {y | cT (barσ σ ϖ h 1) y * red ϖ 1 S * y = red ϖ 1 T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [red_mul_one, red_mul_one, red_cT_one σ ϖ h] at hx
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj_one ϖ y
    simp only [Set.mem_setOf_eq] at hy
    refine ⟨x, ?_, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [red_mul_one, red_mul_one, red_cT_one σ ϖ h]
    exact hy

theorem solCount_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → (solCount σ ϖ S T 1 : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hS' : cT σ S = S ∧ IsUnit S.det := hS
  have hT' : cT σ T = T ∧ IsUnit T.det := hT
  have h1 : cT (barσ σ ϖ hR.fix_ϖ 1) (red ϖ 1 S) = red ϖ 1 S := by
    rw [← red_cT_one σ ϖ hR.fix_ϖ, hS'.1]
  have h2 : cT (barσ σ ϖ hR.fix_ϖ 1) (red ϖ 1 T) = red ϖ 1 T := by
    rw [← red_cT_one σ ϖ hR.fix_ϖ, hT'.1]
  unfold solCount
  rw [red_image_one σ ϖ hR.fix_ϖ S T]
  exact GlobalTheory.T.card_hermitian_representations_residue (R ⧸ lev ϖ 1) (barσ σ ϖ hR.fix_ϖ 1) q ε
    (resAlg_of_isUnrQuad R σ ϖ q ε hR) m n hnm (red ϖ 1 S) (red ϖ 1 T) h1
    (isUnit_det_red_one ϖ S hS'.2) h2 (isUnit_det_red_one ϖ T hT'.2)

end GlobalTheory.CompanionTheory.UnrDens
