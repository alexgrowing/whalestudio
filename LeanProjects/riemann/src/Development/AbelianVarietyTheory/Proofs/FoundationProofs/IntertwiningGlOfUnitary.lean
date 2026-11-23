import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RowActCoefPolyAndUnitaryDense
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem zpow_mul_eq_iff_toNat (d x y : ℂ) (hd : d ≠ 0) (a b : ℤ) :
    d ^ a * x = d ^ b * y ↔ d ^ (a - b).toNat * x = d ^ (b - a).toNat * y := by
  have ha : d ^ a = d ^ (min a b) * d ^ (a - b).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  have hb : d ^ b = d ^ (min a b) * d ^ (b - a).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  rw [ha, hb, mul_assoc, mul_assoc, mul_right_inj' (zpow_ne_zero _ hd)]

theorem exists_coef_sqRep (n : ℕ) (mu : DomWeight n) (f : nablaSq ℂ n mu)
    (l : Module.Dual ℂ (nablaSq ℂ n mu)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : GL (Fin n) ℂ,
      l (sqRep ℂ n mu g f) = (g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift *
        eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2) P := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend l
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.1 n n f L
  refine ⟨rename Prod.swap P, fun g => ?_⟩
  rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, sqRep_coe, sqAct, map_smul, hP, eval_rename]
  simp only [detPow, smul_eq_mul, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem intertwining_gl_of_unitary (n : ℕ) (mu nu : DomWeight n)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu))
    (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu) :
    φ (sqRep ℂ n mu g f) = sqRep ℂ n nu g (φ f) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero]
  obtain ⟨P, hP⟩ := exists_coef_sqRep n mu f (l ∘ₗ φ.toLinearMap)
  obtain ⟨Q, hQ⟩ := exists_coef_sqRep n nu (φ f) l
  let D : MvPolynomial (Fin n × Fin n) ℂ := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  have hD : ∀ m : Matrix (Fin n) (Fin n) ℂ, eval (fun x => m x.1 x.2) D = m.det := by
    intro m
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  have key : ∀ g : GL (Fin n) ℂ, l (φ (sqRep ℂ n mu g f)) = l (sqRep ℂ n nu g (φ f)) ↔
      eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2)
        (D ^ (mu.detShift - nu.detShift).toNat * P - D ^ (nu.detShift - mu.detShift).toNat * Q) = 0 := by
    intro g
    have h1 : l (φ (sqRep ℂ n mu g f)) = _ := hP g
    rw [h1, hQ, zpow_mul_eq_iff_toNat _ _ _ (Matrix.GeneralLinearGroup.det_ne_zero g)]
    simp only [map_sub, map_mul, map_pow, hD, sub_eq_zero]
  have hz := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.2 n _ fun u hu =>
    (key (unitaryIncl n ⟨u, hu⟩)).1 (congrArg l (φ.isIntertwining _ _ ⟨u, hu⟩ f))
  rw [key, hz, map_zero]

end GlobalTheory.Branching
