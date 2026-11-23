import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvROnePow

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Con

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F]

theorem rs_root (s : ℕ) (ζ : Rs F PD.p s) :
    Polynomial.aeval ((ζ : F) - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
  root_Zp PD.p (s + 1) (by rw [add_sub_cancel]; exact rs_pow_N F PD.p s ζ)

def evAt (a : ZMod n) (s : ℕ) (ζ : Rs F PD.p s) : LetA O n →+* F :=
  (evR PD.p (s + 1) hlm (rs_root F s ζ)).toRingHom.comp
    (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)

theorem evAt_apply (a : ZMod n) (s : ℕ) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ x = evR PD.p (s + 1) hlm (rs_root F s ζ) (x a) := rfl

theorem ev_qp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [CharZero F] (s : ℕ) {y : F}
    (hy : Polynomial.aeval y (Zp (O := O) PD.p (s + 1)) = 0) :
    (evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) = 0) ↔
      (y ≠ 0 ∧ (1 + y) ^ PD.p = 1) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Formalism.MainNotions.N.Pv.LocalLengthBound.eat_qp] at hw
  have hq0 : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    have := congrFun hw 0
    simpa [LocWach.q, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀] using this
  have hwu : evR PD.p (s + 1) hlm hy ((w : LetA O n) 0) ≠ 0 := by
    have hu : IsUnit ((w : LetA O n) 0) := (w.isUnit.map (Pi.evalMonoidHom (fun _ => PowerSeries O) 0))
    exact (hu.map (evR PD.p (s + 1) hlm hy)).ne_zero

  have hXq : PowerSeries.X * W.q₀ = (1 + PowerSeries.X) ^ PD.p - 1 := by
    rw [← W.φ₀_X, Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W]
  have hev : y * evR PD.p (s + 1) hlm hy W.q₀ = (1 + y) ^ PD.p - 1 := by
    have := congrArg (evR PD.p (s + 1) hlm hy) hXq
    rwa [map_mul, evR_X, map_sub, evR_onePow, map_one] at this
  have hsplit : evR PD.p (s + 1) hlm hy W.q₀ = evR PD.p (s + 1) hlm hy ((w : LetA O n) 0) *
      evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    rw [hq0, map_mul]
  constructor
  · intro h0
    have hq : evR PD.p (s + 1) hlm hy W.q₀ = 0 := by rw [hsplit, h0, mul_zero]
    refine ⟨fun hy0 => ?_, ?_⟩
    ·
      have hcc := evR_eq_cc PD.p (s + 1) hlm hy hy0 W.q₀
      have hc : PowerSeries.constantCoeff W.q₀ = ((PD.p : ℕ) : O) := by
        have := congrArg (PowerSeries.coeff 1) hXq
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
        rw [this]
        have e : ((1 + PowerSeries.X) ^ PD.p - 1 : PowerSeries O) =
            (((1 + Polynomial.X) ^ PD.p - 1 : Polynomial O) : PowerSeries O) := by
          simp [Polynomial.coe_pow]
        rw [e, Polynomial.coeff_coe, Polynomial.coeff_sub, Polynomial.coeff_one, add_comm,
          Polynomial.coeff_X_add_one_pow]
        simp
      rw [hq, hc, map_natCast] at hcc
      exact (Nat.cast_ne_zero.2 (hpF.out.ne_zero)) hcc.symm
    · have := hev
      rw [hq, mul_zero] at this
      exact (sub_eq_zero.1 this.symm)
  · rintro ⟨hy0, hyp⟩
    have hq : evR PD.p (s + 1) hlm hy W.q₀ = 0 := by
      have := hev
      rw [hyp, sub_self] at this
      exact (mul_eq_zero.1 this).resolve_left hy0
    rw [hsplit] at hq
    exact (mul_eq_zero.1 hq).resolve_left hwu

end Con

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
