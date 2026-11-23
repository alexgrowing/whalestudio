import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.MellinPoly

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < (resCard k : ℝ) := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hq0 : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hz : (resCard k : ℝ) ^ (-SmGL.ord k x) ≠ 0 := (zpow_pos hq _).ne'
  unfold absPow
  simp only [MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [GlobalTheory.LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hz),
    Complex.cpow_def_of_ne_zero hq0, ← Complex.exp_int_mul, ← Complex.ofReal_log (zpow_pos hq _).le,
    Real.log_zpow, ← Complex.ofReal_natCast, ← Complex.ofReal_log hq.le]
  push_cast
  congr 1
  try simp only [Complex.ofReal_intCast, Complex.ofReal_natCast]
  ring

end GlobalTheory.MellinPoly
