import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem star_dotProduct_mulVec_eq {I : Type} [Fintype I] (M : Matrix I I ℂ) (a b : I → ℂ) :
    star (a ⬝ᵥ M *ᵥ b) = star a ⬝ᵥ (Mᴴ)ᵀ *ᵥ star b := by
  simp only [dotProduct, mulVec, Finset.sum_apply, star_sum, star_mul', Pi.star_apply, transpose_apply,
    conjTranspose_apply, Finset.mul_sum, RCLike.star_def]

theorem im_tz_form {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ) (hZ : Zᵀ = Z)
    (hP : (1 - Zᴴ * Z).PosDef) (z w : I → ℂ) :
    (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  obtain ⟨B, hBdef⟩ : ∃ B, B = Zᴴ := ⟨_, rfl⟩
  rw [← hBdef] at hP ⊢
  have hBt : Bᵀ = B := by
    rw [hBdef]; ext i j
    simp only [transpose_apply, conjTranspose_apply]
    rw [← transpose_apply Z i j, hZ]
  have hBh : Bᴴ = Z := by rw [hBdef, conjTranspose_conjTranspose]
  have hdet : IsUnit (1 - B * Z).det := (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
  obtain ⟨H, hHdef⟩ : ∃ H, H = (1 - B * Z)⁻¹ := ⟨_, rfl⟩
  rw [← hHdef]
  have h1 : H * (1 - B * Z) = 1 := by rw [hHdef]; exact Matrix.nonsing_inv_mul _ hdet
  have h2 : (1 - B * Z) * H = 1 := by rw [hHdef]; exact Matrix.mul_nonsing_inv _ hdet
  have hHh : Hᴴ = H := by rw [hHdef]; exact hP.inv.isHermitian.eq
  have hT : (1 - B * Z)ᵀ = 1 - Z * B := by
    rw [transpose_sub, transpose_one, transpose_mul, hZ, hBt]
  have h3 : Hᵀ * (1 - Z * B) = 1 := by
    have := congrArg transpose h2
    rwa [transpose_mul, hT, transpose_one] at this
  have h4 : (1 - Z * B) * Hᵀ = 1 := by
    have := congrArg transpose h1
    rwa [transpose_mul, hT, transpose_one] at this
  have c1 : B * (1 - Z * B) = (1 - B * Z) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have c2 : Z * (1 - B * Z) = (1 - Z * B) * Z := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have K : H * B = B * Hᵀ := by
    calc H * B = H * B * ((1 - Z * B) * Hᵀ) := by rw [h4, Matrix.mul_one]
      _ = H * (B * (1 - Z * B)) * Hᵀ := by simp only [Matrix.mul_assoc]
      _ = H * (1 - B * Z) * (B * Hᵀ) := by rw [c1]; simp only [Matrix.mul_assoc]
      _ = B * Hᵀ := by rw [h1, Matrix.one_mul]
  have K2 : Z * H = Hᵀ * Z := by
    calc Z * H = Hᵀ * (1 - Z * B) * (Z * H) := by rw [h3, Matrix.one_mul]
      _ = Hᵀ * ((1 - Z * B) * Z) * H := by simp only [Matrix.mul_assoc]
      _ = Hᵀ * Z * ((1 - B * Z) * H) := by rw [← c2]; simp only [Matrix.mul_assoc]
      _ = Hᵀ * Z := by rw [h2, Matrix.mul_one]
  have hHB : H = 1 + H * B * Z := by
    have : H * (1 - B * Z) = H - H * B * Z := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    rw [this] at h1
    rw [← h1]; abel
  have hs : star (tz Z w) = star w - B *ᵥ w := by
    unfold tz
    rw [star_sub, star_mulVec, star_star, ← hBdef, ← mulVec_transpose, hBt]
  have dz : ∀ y : I → ℂ, (Z *ᵥ star z) ⬝ᵥ y = star z ⬝ᵥ Z *ᵥ y := by
    intro y
    rw [dotProduct_mulVec (star z), ← mulVec_transpose, hZ]
  have e1 : z ⬝ᵥ H *ᵥ star w = z ⬝ᵥ star w + z ⬝ᵥ (H * B * Z) *ᵥ star w := by
    conv_lhs => rw [hHB]
    rw [add_mulVec, one_mulVec, dotProduct_add]
  have e2 : z ⬝ᵥ H *ᵥ B *ᵥ w = z ⬝ᵥ (H * B) *ᵥ w := by rw [mulVec_mulVec]
  have e3 : (Z *ᵥ star z) ⬝ᵥ H *ᵥ star w = star z ⬝ᵥ (Z * H) *ᵥ star w := by
    rw [dz, mulVec_mulVec]
  have e4 : (Z *ᵥ star z) ⬝ᵥ H *ᵥ B *ᵥ w = star z ⬝ᵥ (Z * H * B) *ᵥ w := by
    rw [dz, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have s3 : star (z ⬝ᵥ (H * B) *ᵥ w) = star z ⬝ᵥ (Z * H) *ᵥ star w := by
    rw [star_dotProduct_mulVec_eq, conjTranspose_mul, hBh, hHh, transpose_mul, hZ, ← K2]
  have s4 : star (star z ⬝ᵥ (Z * H * B) *ᵥ w) = z ⬝ᵥ (H * B * Z) *ᵥ star w := by
    rw [star_dotProduct_mulVec_eq, star_star, conjTranspose_mul, conjTranspose_mul, hBh, hHh, ← hBdef,
      transpose_mul, transpose_mul, hZ, hBt, ← K]
  have main : tz Z z ⬝ᵥ H *ᵥ star (tz Z w) = z ⬝ᵥ star w + star (star z ⬝ᵥ (Z * H * B) *ᵥ w)
      - z ⬝ᵥ (H * B) *ᵥ w - star (z ⬝ᵥ (H * B) *ᵥ w) + star z ⬝ᵥ (Z * H * B) *ᵥ w := by
    rw [hs, s3, s4]
    unfold tz
    rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, e1, e2, e3, e4]
    ring
  rw [main]
  simp only [Complex.add_im, Complex.sub_im, Complex.star_def, Complex.conj_im]
  ring

theorem im_tz_form' : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im :=
  fun Z hZ hP z w => im_tz_form Z hZ hP z w

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
