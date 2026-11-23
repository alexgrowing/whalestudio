import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exp_two_pi_I_div_mul_eq_stdAddChar_mul (p q : ℕ) [NeZero p] [NeZero q] (hpq : Nat.Coprime p q) (T : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (T : ℂ) / ((p * q : ℕ) : ℂ)) =
      ZMod.stdAddChar (((q : ZMod p))⁻¹ * (T : ZMod p)) *
        ZMod.stdAddChar (((p : ZMod q))⁻¹ * (T : ZMod q)) := by
  set A : ℤ := Nat.gcdA q p
  set B : ℤ := Nat.gcdB q p
  have hb : (1 : ℤ) = (q : ℤ) * A + (p : ℤ) * B := by
    have h := Nat.gcd_eq_gcd_ab q p
    rw [Nat.Coprime.gcd_eq_one hpq.symm] at h
    simpa using h
  have hA : ((q : ZMod p))⁻¹ = ((A : ℤ) : ZMod p) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have := congrArg (fun z : ℤ => (z : ZMod p)) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero] at this
    exact this.symm
  have hB : ((p : ZMod q))⁻¹ = ((B : ℤ) : ZMod q) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have := congrArg (fun z : ℤ => (z : ZMod q)) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, zero_add] at this
    exact this.symm
  have e1 : ((q : ZMod p))⁻¹ * (T : ZMod p) = ((A * T : ℤ) : ZMod p) := by
    rw [hA]; push_cast; ring
  have e2 : ((p : ZMod q))⁻¹ * (T : ZMod q) = ((B * T : ℤ) : ZMod q) := by
    rw [hB]; push_cast; ring
  rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hbC : (1 : ℂ) = (q : ℂ) * (A : ℂ) + (p : ℂ) * (B : ℂ) := by exact_mod_cast hb
  push_cast
  field_simp
  linear_combination (T : ℂ) * hbC

end GlobalTheory
