import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionContinuousLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePowStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.SelfPoly

open MvPolynomial

theorem eval_pow_expand (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Θ ((C t * X 0 + X 1) ^ (D + 1)) = ∑ i ∈ Finset.range (D + 2),
      t ^ i * ((D + 1).choose i * Θ (X 0 ^ i * X 1 ^ (D + 1 - i))) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (C t * X 0) ^ i * X 1 ^ (D + 1 - i) * ((D + 1).choose i : MvPolynomial (Fin 2) ℝ)
      = C (t ^ i * (D + 1).choose i) * (X 0 ^ i * X 1 ^ (D + 1 - i)) := by
    rw [C_mul, C_pow, map_natCast]; ring
  rw [this, C_mul', LinearMap.map_smul, smul_eq_mul]; ring

theorem eval_mul_pow_expand (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Θ (X 0 * (C t * X 0 + X 1) ^ D) = ∑ j ∈ Finset.range (D + 1),
      t ^ j * (D.choose j * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j))) := by
  rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : X 0 * ((C t * X 0) ^ j * X 1 ^ (D - j) * (D.choose j : MvPolynomial (Fin 2) ℝ))
      = C (t ^ j * D.choose j) * (X 0 ^ (j + 1) * X 1 ^ (D - j)) := by
    rw [C_mul, C_pow, map_natCast]; ring
  rw [this, C_mul', LinearMap.map_smul, smul_eq_mul]; ring

def poly (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (D + 2),
    Polynomial.C ((D + 1).choose i * Θ (X 0 ^ i * X 1 ^ (D + 1 - i))) * Polynomial.X ^ i

theorem poly_eval (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    (poly Θ D).eval t = Θ ((C t * X 0 + X 1) ^ (D + 1)) := by
  rw [eval_pow_expand, poly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem poly_derivative_eval (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    (poly Θ D).derivative.eval t = ((D : ℝ) + 1) * Θ (X 0 * (C t * X 0 + X 1) ^ D) := by
  rw [eval_mul_pow_expand, poly, map_sum, Polynomial.eval_finsetSum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e₁ : D + 1 - (j + 1) = D - j := Nat.add_sub_add_right D 1 j
  have e₂ : (((D + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) = ((D : ℝ) + 1) * (D.choose j : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq D j).symm
  rw [e₁, Nat.add_sub_cancel]
  calc ((D + 1).choose (j + 1) : ℝ) * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j)) * ((j + 1 : ℕ) : ℝ) * t ^ j
      = (((D + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) * (t ^ j * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j))) := by ring
    _ = _ := by rw [e₂]; ring

end GlobalTheory.HSAmp.SelfPoly

namespace GlobalTheory.HSAmp.SelfPoly

open MvPolynomial HermLB

theorem selfInter_poly : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p) (a a' : ℝ), L.IsSelfInter a → (up L u).IsSelfInter a' →
    ∃ s : Polynomial ℝ, s.eval 0 = a ∧ s.eval 1 = a' ∧
      ∀ t : ℚ, ((D : ℝ) + 1) / 2 * chInt (up L (u.smul t)) D u.u = s.derivative.eval (t : ℝ) := by
  intro H k _ X _ p D hX L u a a' ha ha'
  obtain ⟨Θ, hΘ⟩ := ((H.arExists k X p D hX).2 _ ![fnB u.u u.cInf u.conj, L]).1
  refine ⟨poly Θ D, ?_, ?_, fun t => ?_⟩
  · rw [poly_eval, map_zero, zero_mul, zero_add]
    exact (ha.unique hX (((H.arIso k X p D hX).2 _ _ _ hΘ).1 1)).symm
  · rw [poly_eval, map_one, one_mul]
    have i : (comb ![fnB u.u u.cInf u.conj, L] fun _ => 1).Isometric (up L u) := icls_eq_iff.1 (by
      show _ = (L.raise u.u u.cInf u.conj).icls
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_comb, Fin.sum_univ_two,
        one_smul, one_smul, add_comm]
      rfl)
    rw [ha'.unique hX (i.isSelfInter hX (hΘ.1 _))]
    simp [lin, Fin.sum_univ_two]
  · rw [poly_derivative_eval]
    have hd : (t.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 t.den_nz
    have hq : (t.den : ℝ) * (t : ℝ) = t.num := by
      rw [Rat.cast_def]; field_simp
    let n : Fin 2 → ℤ := ![t.num, t.den]
    have h₁ := GlobalTheory.SelfCont.mixed_eq H hX u.cInf u.conj L hΘ n
    have h₂ := (GlobalTheory.SelfCont.isometric_comb_raise u.cInf u.conj L n).chInt_eq D u.u
    have h₃ : ((zp L (n 1)).raise (fun σ y => (n 0 : ℝ) * u.u σ y) (fun σ y => (u.cInf σ y).const_mul _)
        (GlobalTheory.SelfCont.isConj_mul u.conj _)).Isometric ((up L (u.smul t)).pow t.den) := icls_eq_iff.1 (by
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_pow]
      show _ = t.den • ((L.raise (u.smul t).u (u.smul t).cInf (u.smul t).conj).icls)
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_zp, smul_add, ← natCast_zsmul,
        ← natCast_zsmul, ← GlobalTheory.SelfCont.icls_fnB_mul (u.smul t).cInf (u.smul t).conj]
      congr 1
      refine icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => ?_)
      show (t.den : ℤ) * ((t : ℝ) * u.u σ y) = (t.num : ℝ) * u.u σ y
      rw [← hq]; push_cast; ring)
    have h₄ := GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow k X p D hX (up L (u.smul t)) t.den u.u
    have h₅ : (lin fun i => (n i : ℝ)) = C (t.den : ℝ) * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) := by
      simp only [lin, Fin.sum_univ_two, n, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [mul_add, ← mul_assoc, ← C_mul, hq]; push_cast; ring
    have h₆ : Θ (MvPolynomial.X 0 * (lin fun i => (n i : ℝ)) ^ D) = (t.den : ℝ) ^ D * Θ (MvPolynomial.X 0 * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) ^ D) := by
      rw [h₅, mul_pow, ← C_pow, mul_left_comm, C_mul', LinearMap.map_smul, smul_eq_mul]
    have key : (t.den : ℝ) ^ D * chInt (up L (u.smul t)) D u.u =
        (t.den : ℝ) ^ D * (2 * Θ (MvPolynomial.X 0 * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) ^ D)) := by
      rw [← h₄, ← h₃.chInt_eq, ← h₂]
      linarith
    have := mul_left_cancel₀ (pow_ne_zero D hd) key
    rw [this]; ring

end GlobalTheory.HSAmp.SelfPoly
