import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseLocal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic

theorem ti_ti {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (g : GL n R) :
    ti (ti g) = g := by
  apply Units.ext
  change (g.val.transpose).transpose = g.val
  rw [Matrix.transpose_transpose]

theorem rational_sign_diag_adelic : dia dl3 = (dg 1 (-1) 1 : GL (Fin 3) 𝔸[ℚ]) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dl3, dg, AdelicGLn.diagonal]

theorem conj_uni {R : Type*} [CommRing R] (x y z : R) :
    w3 * ti (dg 1 (-1) 1 : GL (Fin 3) R) * ti (uni x y z) =
      uni z (x * z - y) x * (w3 * ti (dg 1 (-1) 1 : GL (Fin 3) R)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w3, ti, dg, uni, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct] <;> ring

theorem conj_cen {R : Type*} [CommRing R] (a : Rˣ) :
    w3 * ti (dg 1 (-1) 1 : GL (Fin 3) R) * ti (dg a a a) =
      dg a⁻¹ a⁻¹ a⁻¹ * (w3 * ti (dg 1 (-1) 1 : GL (Fin 3) R)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w3, ti, dg, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct] <;> ring

theorem tr_apply (W : G3 → ℂ) (g : G3) : tr W g = W (w3 * ti (dia dl3) * ti g) := by
  change W (w3 * ti (dia dl3 * g)) = _
  rw [GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, mul_assoc]

theorem main :
    (∀ (W : G3 → ℂ) (g : G3), tr W g = W (w3 * ti (dia dl3) * ti g)) ∧
    (∀ (W : G3 → ℂ) (h g : G3), tr W (g * h) = tr (fun x => W (x * ti h)) g) ∧
    Function.Injective tr ∧
    (∀ W : G3 → ℂ, (∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g) →
      ∀ x y z g, tr W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * tr W g) ∧
    (∀ W : G3 → ℂ, (∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) →
      ∀ (a : (𝔸[ℚ])ˣ) g, tr W (dg a a a * g) = tr W g) := by
  refine ⟨tr_apply, ?_, ?_, ?_, ?_⟩
  · intro W h g
    rw [tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul]
    simp only [mul_assoc]
  · intro W W' e
    funext x
    have := congrFun e (ti ((w3 * ti (dia dl3))⁻¹ * x))
    rwa [tr_apply, tr_apply, ti_ti, mul_inv_cancel_left] at this
  · intro W hW x y z g
    rw [tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, ← mul_assoc, rational_sign_diag_adelic, conj_uni, mul_assoc,
      hW, add_comm z x]
  · intro W hW a g
    rw [tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, ← mul_assoc, rational_sign_diag_adelic, conj_cen]
    have := hW a⁻¹ (w3 * ti (dg 1 (-1) 1 : GL (Fin 3) 𝔸[ℚ]) * ti g)
    rw [mul_assoc, this]

end GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic

end
