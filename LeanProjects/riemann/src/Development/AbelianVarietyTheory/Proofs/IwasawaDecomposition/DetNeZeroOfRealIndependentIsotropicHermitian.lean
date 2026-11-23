import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem det_ne_zero_of_real_indep_isotropic : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E : Fin g → Fin g → ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → LinearIndependent ℝ E → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (Matrix.of fun k i => E i k).det ≠ 0 := by
  intro g Hm E hpos hind him
  have hL : ∀ (a : Fin g → ℝ) (w : Fin g → ℂ), hermForm Hm (∑ i, (a i : ℂ) • E i) w
      = ∑ i, (a i : ℂ) * hermForm Hm (E i) w := by
    intro a w
    simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hR : ∀ (b : Fin g → ℝ) (z : Fin g → ℂ), hermForm Hm z (∑ j, (b j : ℂ) • E j)
      = ∑ j, (b j : ℂ) * hermForm Hm z (E j) := by
    intro b z
    have hs : star (∑ j, (b j : ℂ) • E j) = ∑ j, (b j : ℂ) • star (E j) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext k
      simp
    simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have him0 : ∀ a b : Fin g → ℝ,
      (hermForm Hm (∑ i, (a i : ℂ) • E i) (∑ j, (b j : ℂ) • E j)).im = 0 := by
    intro a b
    rw [hL]
    simp only [hR, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp [Complex.mul_im, him i j]
  have hsmulL : ∀ (c : ℂ) (z w : Fin g → ℂ), hermForm Hm (c • z) w = c * hermForm Hm z w := by
    intro c z w
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have hreal : ∀ a : Fin g → ℝ, (∑ i, (a i : ℂ) • E i) = 0 → a = 0 := by
    intro a h0
    have h1 : ∑ i, a i • E i = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      simp
    have := Fintype.linearIndependent_iff.mp hind a h1
    funext i
    exact this i
  have hC : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsplit : (∑ i, (((c i).re : ℝ) : ℂ) • E i) + Complex.I • (∑ i, (((c i).im : ℝ) : ℂ) • E i) = 0 := by
      rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      exact (mul_comm Complex.I _ ▸ Complex.re_add_im (c i))
    set X := ∑ i, (((c i).re : ℝ) : ℂ) • E i with hX
    set Y := ∑ i, (((c i).im : ℝ) : ℂ) • E i with hY
    have hXY : X = (-Complex.I) • Y := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hsplit
    have hY0 : Y = 0 := by
      by_contra hne
      have hp := hpos Y hne
      have h2 := him0 (fun i => (c i).re) (fun i => (c i).im)
      change (hermForm Hm X Y).im = 0 at h2
      rw [hXY, hsmulL] at h2
      simp [Complex.mul_im] at h2
      linarith
    have hX0 : X = 0 := by rw [hXY, hY0, smul_zero]
    have hre := hreal (fun i => (c i).re) hX0
    have him' := hreal (fun i => (c i).im) hY0
    intro i
    apply Complex.ext
    · simpa using congrFun hre i
    · simpa using congrFun him' i
  have hcol : LinearIndependent ℂ (Matrix.of fun k i => E i k : Matrix (Fin g) (Fin g) ℂ).col := hC
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hcol
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
