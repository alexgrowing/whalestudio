import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem charpoly_eq_sharp (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) (γ : GRat σ J) :
    γ.1.1.charpoly = sharp σ n γ.1.1.charpoly := by
  have h : (γ.1.1.map (σ : E →+* E))ᵀ * J * γ.1.1 = J := γ.2
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 (Ne.isUnit hJ)
  obtain ⟨U, hU⟩ := hJu
  have hg : IsUnit γ.1.1 := γ.1.isUnit
  have hgd : IsUnit γ.1.1.det := (Matrix.isUnit_iff_isUnit_det _).1 hg
  have hJd : IsUnit J.det := Ne.isUnit hJ
  set g := γ.1.1 with hgdef
  have h2 : (g.map (σ : E →+* E))ᵀ = J * g⁻¹ * J⁻¹ := by
    have : (g.map (σ : E →+* E))ᵀ * J = J * g⁻¹ := by
      conv_rhs => rw [← h]
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hgd]
    rw [← this, Matrix.mul_nonsing_inv_cancel_right _ _ hJd]
  set c : E := (-1) ^ n * Ring.inverse g.det with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (inv_ne_zero hgd.ne_zero)
  have hdeg : g.charpoly.natDegree = n := by simp
  have h3 : g.charpoly.map (σ : E →+* E) = C c * reflect n g.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose, h2, ← hU, Matrix.charpoly_units_conj,
      Matrix.charpoly_inv _ hg, ← Matrix.reverse_charpoly, Polynomial.reverse, hdeg, hc]
    simp
  have h4 : σ (g.charpoly.eval 0) = c := by
    have e : σ (g.charpoly.eval 0) = (g.charpoly.map (σ : E →+* E)).coeff 0 := by
      rw [coeff_map, coeff_zero_eq_eval_zero]; rfl
    have m : g.charpoly.coeff n = 1 := by
      have := (Matrix.charpoly_monic g).coeff_natDegree
      rwa [hdeg] at this
    rw [e, h3, coeff_C_mul, coeff_reflect, revAt_zero, m, mul_one]
  unfold sharp
  rw [h4, h3, reflect_C_mul, reflect_reflect, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0, C_1, one_mul]

end GlobalTheory.TrEll
