import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFracOfAdjoinEqTop
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

set_option autoImplicit false in
open KaehlerDifferential in

theorem _root_.GlobalTheory.PD.rA_single_polyEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x →
    ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] _root_.GlobalTheory.PD.rA k x {i},
      ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  intro k _ F _ _ d x hP i
  refine ⟨_root_.GlobalTheory.PD.Model.chartEquiv k x hP i, fun j => ?_⟩
  simp [_root_.GlobalTheory.PD.Model.chartEquiv, _root_.GlobalTheory.PD.Model.yc,
    AlgebraicIndependent.aevalEquiv_apply_coe]

end GlobalTheory.PD
