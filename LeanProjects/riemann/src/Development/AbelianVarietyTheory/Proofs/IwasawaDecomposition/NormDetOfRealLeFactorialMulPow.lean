import Mathlib
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem psd_real_quad_single (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosSemidef) (i j : Fin g)
    (hij : i ≠ j) (c : ℝ) : 0 ≤ Y i i + c * Y i j + c * Y j i + c * c * Y j j := by
  have h := hY.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j c)
  simp only [star_trivial, mulVec_add, add_dotProduct, dotProduct_add, mulVec_single,
    single_dotProduct, dotProduct_single] at h
  simp [Pi.single_apply, hij, hij.symm] at h
  linarith

theorem abs_entry_le_of_psd_le (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ)
    (hY : Y.PosSemidef) (hMY : (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) (i j : Fin g) :
    |Y i j| ≤ M := by
  have hdiag : ∀ k, Y k k ≤ M := by
    intro k
    have := hMY.diag_nonneg (i := k)
    simp at this
    linarith
  have hsym : Y j i = Y i j := by
    have := congrFun (congrFun hY.isHermitian j) i
    simpa [conjTranspose_apply] using this.symm
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg (hY.diag_nonneg (i := i))]
    exact hdiag i
  · have h1 := psd_real_quad_single g Y hY i j hij 1
    have h2 := psd_real_quad_single g Y hY i j hij (-1)
    have hi := hdiag i
    have hj := hdiag j
    rw [hsym] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith

theorem det_map_ofReal_norm_le : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef →
    (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef →
    ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  intro g Y M _ hY hMY
  have hmap : (Y.map Complex.ofReal).det = ((Y.det : ℝ) : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom Y
    exact this.symm
  rw [hmap, Complex.norm_real, Real.norm_eq_abs]
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := M) (A := Y)
    (fun i j => abs_entry_le_of_psd_le g Y M hY hMY i j)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

end GlobalTheory
