import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped Matrix CategoryTheory.Obj Topology in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.det_ne_zero_of_im_hermForm_eq_int : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u u).re) → LinearIndependent ℝ lam → Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 := by
  intro g r Hm lam M hpos hli hspan hM hdet
  have hdet' : (M.map (Int.cast : ℤ → ℝ)).det = 0 := by
    have h := RingHom.map_det (Int.castRingHom ℝ) M
    rw [hdet, map_zero] at h
    exact h.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
  set w : Fin g → ℂ := ∑ j, v j • lam j with hwdef
  have hw0 : w ≠ 0 := by
    intro hw
    apply hv0
    funext j
    exact Fintype.linearIndependent_iff.mp hli v hw j
  have hlin : ∀ x : Fin g → ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x w = ∑ j, v j • _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x (lam j) := by
    intro x
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, hwdef, star_sum, star_smul, star_trivial, Matrix.mulVec_sum,
      Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]
  have hlamw : ∀ i, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) w).im = 0 := by
    intro i
    have hrow := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hrow
    rw [hlin, Complex.im_sum]
    simp only [Complex.smul_im, hM, smul_eq_mul]
    rw [← hrow]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hall : ∀ x, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x w).im = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hlamw i
    | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
    | add y z _ _ hy hz =>
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct, Complex.add_im] at hy hz ⊢
      rw [hy, hz, add_zero]
    | smul c y _ hy =>
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im] at hy ⊢
      rw [hy, smul_zero]
  have hI := hall (Complex.I • w)
  have hre := hpos w hw0
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add] at hI hre
  linarith

end GlobalTheory
