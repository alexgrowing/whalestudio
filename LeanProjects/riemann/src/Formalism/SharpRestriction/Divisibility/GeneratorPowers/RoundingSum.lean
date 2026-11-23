import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FramedFamilyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

theorem bOf_zsmul_right (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (a : ℤ) (b v : D.toPre.X) :
    bOf D.toPre Q v (a • b) = a * bOf D.toPre Q b v := by
  rw [bOf_comm]
  have h := map_zsmul (AddMonoidHom.mk' (fun x => bOf D.toPre Q x v) (fun x y => bOf_add_left (hϖ := hϖ) (D := D) (Q := Q) (hQ := hQ) x y v)) a b
  simpa using h

private theorem bOf_self_lemma (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (x : D.toPre.X) :
    bOf D.toPre Q x x = 2 * Q x := by
  have h1 := bOf_zsmul_right hϖ hQ (-1) x x
  rw [neg_one_zsmul] at h1
  have h2 : bOf D.toPre Q x (-x) = Q (x + -x) - Q x - Q (-x) := rfl
  rw [show x + -x = (0 : D.toPre.X) by abel, Q_zero (hϖ := hϖ) (D := D) (Q := Q) (hQ := hQ), Q_neg (hϖ := hϖ) (D := D) (Q := Q) (hQ := hQ)] at h2
  linarith

theorem Q_zsmul (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (a : ℤ) (b : D.toPre.X) :
    Q (a • b) = a ^ 2 * Q b := by
  have h1 := bOf_self_lemma hϖ hQ (a • b)
  have h2 := bOf_zsmul_right hϖ hQ a b (a • b)
  have h3 := bOf_zsmul_right hϖ hQ a b b
  have h4 := bOf_self_lemma hϖ hQ b
  rw [h3, h4] at h2
  nlinarith [h1, h2]

theorem Q_add_zsmul (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (v b : D.toPre.X) (a : ℤ) :
    Q (v + a • b) = Q v + a * bOf D.toPre Q b v + a ^ 2 * Q b := by
  have h1 : bOf D.toPre Q v (a • b) = Q (v + a • b) - Q v - Q (a • b) := rfl
  rw [bOf_zsmul_right hϖ hQ, Q_zsmul hϖ hQ] at h1
  linarith

theorem Q_nonneg (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (χ : D.toPre.X) : 0 ≤ Q χ := by
  by_cases hχ : χ = 0
  · rw [hχ, Q_zero (hϖ := hϖ) (D := D) (Q := Q) (hQ := hQ)]
  · exact le_trans zero_le_one (Q_pos (hϖ := hϖ) (D := D) (Q := Q) (hQ := hQ) hχ)

theorem gap (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (χ' : D.toPre.X) (f : D.toPre.X →+ D.toPre.X)
    (hmin : ∀ z, Q χ' ≤ Q (χ' + f z)) (hf : ∀ z, z ≠ 0 → f z ≠ 0) (k : ℕ) (hk : 2 ≤ k)
    (z : D.toPre.X) (hz : z ≠ 0) : Q χ' < Q (χ' + k • f z) := by
  have hw : f z ≠ 0 := hf z hz
  have hq := Q_pos (hϖ := hϖ) (D := D) (Q := Q) (hQ := hQ) hw
  have e := Q_add_zsmul hϖ hQ χ' (f z) (k : ℤ)
  have hk' : ((k : ℤ) • f z) = k • f z := by simp
  rw [hk'] at e
  have m1 := hmin z
  have m2 := hmin (-z)
  have e1 := Q_add_zsmul hϖ hQ χ' (f z) 1
  have e2 := Q_add_zsmul hϖ hQ χ' (f z) (-1)
  rw [one_zsmul] at e1
  rw [neg_one_zsmul] at e2
  rw [map_neg] at m2
  have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have A : 0 ≤ (k : ℤ) * (bOf D.toPre Q (f z) χ' + Q (f z)) := mul_nonneg (by linarith) (by linarith)
  have C : 0 < (k : ℤ) * ((k : ℤ) - 1) * Q (f z) := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  rw [e]
  nlinarith [A, C]

end Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt
