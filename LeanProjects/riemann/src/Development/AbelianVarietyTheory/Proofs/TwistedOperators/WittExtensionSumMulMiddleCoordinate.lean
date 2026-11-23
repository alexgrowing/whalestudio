import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BumpMix

variable {D : D7}

theorem witt_extension_sum_mul_middle_coordinate {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ d.j0 = w₀ := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_j0,
    HypDec.pY_j0, HypDec.p0_j0, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem coord_jX {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ d.jX = x := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jX,
    HypDec.pY_jX, HypDec.p0_jX, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem coord_jY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ d.jY = a := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jY,
    HypDec.pY_jY, HypDec.p0_jY, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem eq_coords {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (u : WO S T) :
    u = d.extX T (u ⬝ d.jX) + d.ext0 T (u ⬝ d.j0) + d.extY T (u ⬝ d.jY) :=
  ((d.coordS T).symm_apply_apply u).symm

theorem symplOH_Y_X {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) :
    symplOH S T (d.extY T a) (d.extX T x) = -trHalf D (pairS T x a) := by
  rw [symplOH_skew, d.symplOH_extX_extY]

def poinX (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (β : Mx D T.rank ρ → ℂ) (u : WO S T) : ℂ :=
  ∑' γ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
    ψ (trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) * β (u ⬝ d.jX + rat γ)

theorem poinX_coords (ψ : AddChar (AF D.host.F) ℂ) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (β : Mx D T.rank ρ → ℂ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    poinX ψ d T β (d.extY T a + d.extX T x + d.ext0 T w₀) =
      ∑' γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (trHalf D (pairS T (x + 2 • rat γ) a)) * β (x + rat γ) := by
  simp only [poinX, coord_jX, coord_jY]

example (ψ : AddChar (AF D.host.F) ℂ) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    poinX ψ d T 0 = 0 := by
  funext u; simp [poinX]

end GlobalTheory.BumpMix

end
