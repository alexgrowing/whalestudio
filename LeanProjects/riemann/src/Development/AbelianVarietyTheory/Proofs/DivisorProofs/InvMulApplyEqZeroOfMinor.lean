import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

theorem det_submatrix_mul_of_minor {N : ℕ} {A : Type} [CommRing A] (M g h : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1))
    (u : A) (hu : ∀ I, minor h l I = u * minor g l I) (r : Fin l → Fin N) :
    ((M * h).submatrix r (Fin.castLE l.is_le)).det = u * ((M * g).submatrix r (Fin.castLE l.is_le)).det := by
  rw [det_submatrix_mul_eq_sum_minors, det_submatrix_mul_eq_sum_minors, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have := hu I
  rw [minor, minor] at this
  rw [this]
  ring

theorem inv_mul_apply_eq_zero_of_minor {N : ℕ} {A : Type} [CommRing A] (g h : GL (Fin N) A) (l : Fin (N + 1))
    (u : Aˣ) (hu : ∀ I, minor h.1 l I = u * minor g.1 l I) (i j : Fin N) (hj : (j : ℕ) < l) (hi : (l : ℕ) ≤ i) :
    (g⁻¹ * h).1 i j = 0 := by
  have H (r : Fin l → Fin N) := det_submatrix_mul_of_minor (g⁻¹).1 g.1 h.1 l u hu r
  simp only [← Units.val_mul, inv_mul_cancel, Units.val_one] at H
  set c := (g⁻¹ * h).1
  set c₁ := c.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) with hc₁
  have h₁ : c₁.det = u := by
    rw [hc₁, H, submatrix_one _ (Fin.castLE_injective _), det_one, mul_one]
  have h₂ : cramer c₁ᵀ (fun k => c i (Fin.castLE l.is_le k)) = 0 := by
    funext k
    have e : c₁.updateRow k (fun k => c i (Fin.castLE l.is_le k)) =
        c.submatrix (Function.update (Fin.castLE l.is_le) k i) (Fin.castLE l.is_le) := by
      ext p q
      by_cases hp : p = k
      · subst hp
        simp
      · simp [hc₁, updateRow_ne hp, Function.update_of_ne hp]
    rw [cramer_transpose_apply, e, H, det_eq_zero_of_row_eq_zero k, mul_zero, Pi.zero_apply]
    intro q
    rw [submatrix_apply, Function.update_self]
    refine one_apply_ne fun e => ?_
    have : (i : ℕ) = q := congrArg Fin.val e
    omega
  have h₃ := congrFun (mulVec_cramer c₁ᵀ (fun k => c i (Fin.castLE l.is_le k))) ⟨j, hj⟩
  rw [h₂, mulVec_zero, det_transpose, h₁] at h₃
  exact (Units.mul_right_eq_zero u).1 h₃.symm

theorem flagPt_eq_iff_below : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)) (A : Type)
    [CommRing A] (g h : ι → GL (Fin N) A),
    flagPt a l g = flagPt a l h ↔ ∀ τ i j, Below a l τ i j → ((g τ)⁻¹ * h τ).1 i j = 0 := by
  intro ι κ _ _ N a l A _ g h
  constructor
  · rintro e _ i j ⟨k, rfl, hj, hi⟩
    obtain ⟨u, hu⟩ := (flagPt_eq_iff a l g h).1 e k
    exact inv_mul_apply_eq_zero_of_minor _ _ _ u hu i j hj hi
  · intro H
    have := flagPt_mul a l g (g⁻¹ * h) fun k i j hj hi => H (a k) i j ⟨k, rfl, hj, hi⟩
    rw [mul_inv_cancel_left] at this
    exact this.symm

end GlobalTheory.FlagZ
