import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_self (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b := by
  have h := p.sec_pr (p.sec a * p.sec b)
  rw [map_mul, p.pr_sec, p.pr_sec] at h
  rw [h, ← mul_assoc, sec_self]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  have h := p.sec_pr 1
  rwa [map_one, mul_one] at h

theorem splitPlaceSection_add_complement_mul (p : SplitPt D k) (a b : k) :
    (p.sec a + (1 - p.e)) * (p.sec b + (1 - p.e)) = p.sec (a * b) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p a
  have hb := sec_self p b
  rw [sec_mul]
  linear_combination (-1 : AE D) * ha + (-1 : AE D) * hb + he

def idl (p : SplitPt D k) : kˣ →* (AE D)ˣ where
  toFun a := ⟨p.sec a + (1 - p.e), p.sec ((a⁻¹ : kˣ) : k) + (1 - p.e),
    by rw [splitPlaceSection_add_complement_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, sec_one]; ring,
    by rw [splitPlaceSection_add_complement_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, sec_one]; ring⟩
  map_one' := Units.ext (by simp only [Units.val_one, sec_one]; ring)
  map_mul' a b := Units.ext (by simp only [Units.val_mul, splitPlaceSection_add_complement_mul])

theorem idl_val (p : SplitPt D k) (a : kˣ) : ((idl p a : (AE D)ˣ) : AE D) = p.sec (a : k) + (1 - p.e) := rfl

def lam (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ) : kˣ →* ℂˣ where
  toFun a := Units.mk0 ((χ (idl p a) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) ^ r : ℝ) : ℂ))
    (mul_ne_zero (Circle.coe_ne_zero _)
      (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _) r).ne'))
  map_one' := Units.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV])
  map_mul' a b := Units.ext (by
    simp only [map_mul, Units.val_mk0, Units.val_mul, Circle.coe_mul, GlobalTheory.SplitLinear.absFin_mul,
      Real.mul_rpow (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le, Complex.ofReal_mul]
    ring)

theorem lam_val (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ) (a : kˣ) :
    ((lam p χ r a : ℂˣ) : ℂ) = (χ (idl p a) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) ^ r : ℝ) : ℂ) := rfl

end GlobalTheory.SplitLinAt
end
