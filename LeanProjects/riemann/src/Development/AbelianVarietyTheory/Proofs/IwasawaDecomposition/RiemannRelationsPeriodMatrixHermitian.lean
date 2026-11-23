import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.riemann_relations_period_matrix : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin d → Fin g → ℂ) (τ : Fin d → Fin d → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) ∧ ∀ i j, τ i j - τ j i = ((hermForm Hm (F i) (F j)).im : ℂ) := by
  intro g d Hm E F τ hH hpos hF hA hFE
  have hexp : ∀ z w : Fin g → ℂ, hermForm Hm z w = ∑ x, ∑ y, z x * Hm x y * star (w y) := by
    intro z w; unfold hermForm; simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [Pi.star_apply]; ring
  have lin1 : ∀ (c : Fin d → ℂ) (w : Fin g → ℂ),
      hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
    intro c w
    unfold hermForm
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have symm : ∀ z w : Fin g → ℂ, hermForm Hm w z = star (hermForm Hm z w) := by
    intro z w
    simp only [hexp, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show star (Hm x y) = Hm y x from hH.apply y x]; ring
  have lin2 : ∀ (c : Fin d → ℂ) (z : Fin g → ℂ),
      hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
    intro c z
    rw [symm, lin1, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul', ← symm]
  set a : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hA])
  have asymm : aᵀ = a := by
    ext i k; simp only [a, Matrix.transpose_apply, Matrix.of_apply]; rw [symm]; simp
  set Y : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).im with hY
  set X : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).re with hX
  have hYA : Yᵀ * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hF j, lin1] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero] at h
    simpa [Matrix.mul_apply, Matrix.one_apply, Y] using h
  have hAY : a * Y = 1 := by
    have h := congrArg Matrix.transpose hYA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, asymm, Matrix.transpose_one] at h
  have hYs : Yᵀ = Y := by
    calc Yᵀ = Yᵀ * (a * Y) := by rw [hAY, Matrix.mul_one]
    _ = (Yᵀ * a) * Y := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hYA, Matrix.one_mul]
  have e1 : ∀ i m, ∑ p, Y p i * a p m = if i = m then 1 else 0 := fun i m => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hYA i) m
  have e2 : ∀ p j, ∑ m, a p m * Y m j = if p = j then 1 else 0 := fun p j => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hAY p) j
  have ys : ∀ i j, Y i j = Y j i := fun i j => by
    simpa using (congrFun (congrFun hYs j) i)
  refine ⟨fun v hv => ?_, fun i j => ?_⟩
  · have him : (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im = v ⬝ᵥ (Y *ᵥ v) := by
      simp only [Complex.im_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Y, Complex.mul_im]; ring
    rw [him]
    set w := Y *ᵥ v with hw
    have hAw : a *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hAY, Matrix.one_mulVec]
    set Q : Fin g → ℂ := ∑ i, ((w i : ℝ) : ℂ) • E i with hQ
    have hQE : ∀ k, (hermForm Hm Q (E k)).re = v k := by
      intro k
      rw [hQ, lin1, ← hAw]
      simp only [hAr, Complex.re_sum, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Complex.mul_re]
      rw [show a k i = a i k from by simpa using congrFun (congrFun asymm i) k]; ring
    have hQQ : (hermForm Hm Q Q).re = v ⬝ᵥ w := by
      have hl := lin2 (fun i => (w i : ℂ)) Q
      rw [← hQ] at hl
      rw [hl]
      simp only [Complex.re_sum, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hQE k]; simp [Complex.mul_re]; ring
    have hQ0 : Q ≠ 0 := by
      intro h; apply hv; funext k; rw [← hQE k, h]; simp [hermForm]
    rw [← hQQ]; exact hpos Q hQ0
  · have key : (hermForm Hm (F i) (F j)).im = X i j - X j i := by
      rw [hF i, lin1]
      simp only [hF j, lin2, hAr, Complex.im_sum, Finset.mul_sum]
      have h1 : ∀ p m, ((τ p i) * (star (τ m j) * (a p m : ℂ))).im
          = Y p i * a p m * X m j - X p i * (a p m * Y m j) := fun p m => by
        simp [Y, X, Complex.mul_im, Complex.mul_re]; ring
      simp only [h1, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, e1, e2]
      simp [X]
    apply Complex.ext
    · simp [key, X]
    · simp [Y] at ys; simp [ys j i]
