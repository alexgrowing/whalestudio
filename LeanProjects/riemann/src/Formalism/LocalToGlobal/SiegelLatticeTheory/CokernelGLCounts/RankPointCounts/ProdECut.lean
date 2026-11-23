import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

abbrev MP (p : PlF D) : Type := Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep

abbrev GLp (p : PlF D) : Type := Matrix.GeneralLinearGroup (Fin (D.R.rS + 1)) (D.s.atP p).Ep

def Y0 (p : PlF D) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM (ptMat w))

def StP (p : PlF D) : Subgroup (GLp p × (GLp p)ᵐᵒᵖ) where
  carrier := {x | IsLoUni (x.1 : MP p) ∧ IsUpUni ((x.2.unop : GLp p) : MP p) ∧
    (x.1 : MP p) * Y0 M δ u u' w p * ((x.2.unop : GLp p) : MP p) = Y0 M δ u u' w p}
  one_mem' := ⟨ZsVolGrp.isLoUni_one, ZsVolGrp.isUpUni_one, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨?_, ?_, ?_⟩
    · show IsLoUni ((x.1 * y.1 : GLp p) : MP p)
      rw [Units.val_mul]; exact ZsVolGrp.isLoUni_mul hx1 hy1
    · show IsUpUni (((x.2 * y.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact ZsVolGrp.isUpUni_mul hy2 hx2
    · show ((x.1 * y.1 : GLp p) : MP p) * _ * (((x.2 * y.2).unop : GLp p) : MP p) = _
      rw [MulOpposite.unop_mul, Units.val_mul, Units.val_mul]
      calc (x.1 : MP p) * (y.1 : MP p) * Y0 M δ u u' w p *
            (((y.2.unop : GLp p) : MP p) * ((x.2.unop : GLp p) : MP p))
          = (x.1 : MP p) * ((y.1 : MP p) * Y0 M δ u u' w p * ((y.2.unop : GLp p) : MP p)) *
              ((x.2.unop : GLp p) : MP p) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hy3, hx3]
  inv_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    refine ⟨?_, ?_, ?_⟩
    · show IsLoUni ((x.1⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.isLoUni_inv hx1).1
    · show IsUpUni (((x.2⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.isUpUni_inv hx2).1
    · show ((x.1⁻¹ : GLp p) : MP p) * _ * (((x.2⁻¹).unop : GLp p) : MP p) = _
      rw [MulOpposite.unop_inv]
      have h1 : ((x.1⁻¹ : GLp p) : MP p) * (x.1 : MP p) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : ((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      conv_lhs => rw [← hx3]
      calc ((x.1⁻¹ : GLp p) : MP p) * ((x.1 : MP p) * Y0 M δ u u' w p * ((x.2.unop : GLp p) : MP p)) *
            (((x.2.unop)⁻¹ : GLp p) : MP p)
          = (((x.1⁻¹ : GLp p) : MP p) * (x.1 : MP p)) * Y0 M δ u u' w p *
              (((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p)) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

def AP (p : PlF D) : Subgroup (StP M δ u u' w p) where
  carrier := {x | Formalism.MainNotions.S.TieN.IntLow (M p) ((x.1.1 : GLp p) : MP p) ∧
    Formalism.MainNotions.S.TieN.IntUp (M p) ((x.1.2.unop : GLp p) : MP p)}
  one_mem' := ⟨ZsVolGrp.intLow_one _, ZsVolGrp.intUp_one _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1.1 * y.1.1 : GLp p)) : MP p)
      rw [Units.val_mul]; exact ZsVolGrp.intLow_mul _ hx1 hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (((x.1.2 * y.1.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact ZsVolGrp.intUp_mul _ hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1.1)⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.intLow_inv _ hx1).1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) ((((x.1.2)⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.intUp_inv _ hx2).1

def CP (p : PlF D) (Lp Lpi Up Upi : MP p) (hL : Lpi * Lp = 1) (hU : Up * Upi = 1) : Subgroup (StP M δ u u' w p) where
  carrier := {x | Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1.1 : GLp p) : MP p) * Lpi) ∧
    Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((x.1.2.unop : GLp p) : MP p) * Up)}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((1 : GLp p) : MP p) * Lpi)
      rw [Units.val_one, Matrix.mul_one, show Lp * Lpi = 1 from (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hL]
      exact ZsVolGrp.intLow_one _
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((1 : GLp p) : MP p) * Up)
      rw [Units.val_one, Matrix.mul_one, show Upi * Up = 1 from (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hU]
      exact ZsVolGrp.intUp_one _
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1.1 * y.1.1 : GLp p) : MP p) * Lpi)
      rw [Units.val_mul]
      have e : Lp * ((x.1.1 : GLp p) * (y.1.1 : GLp p) : MP p) * Lpi =
          (Lp * ((x.1.1 : GLp p) : MP p) * Lpi) * (Lp * ((y.1.1 : GLp p) : MP p) * Lpi) := by
        rw [show (Lp * ((x.1.1 : GLp p) : MP p) * Lpi) * (Lp * ((y.1.1 : GLp p) : MP p) * Lpi) =
          Lp * ((x.1.1 : GLp p) : MP p) * (Lpi * Lp) * ((y.1.1 : GLp p) : MP p) * Lpi by simp only [Matrix.mul_assoc],
          hL, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      rw [e]; exact ZsVolGrp.intLow_mul _ hx1 hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * (((x.1.2 * y.1.2).unop : GLp p) : MP p) * Up)
      rw [MulOpposite.unop_mul, Units.val_mul]
      have e : Upi * (((y.1.2.unop : GLp p) : MP p) * ((x.1.2.unop : GLp p) : MP p)) * Up =
          (Upi * ((y.1.2.unop : GLp p) : MP p) * Up) * (Upi * ((x.1.2.unop : GLp p) : MP p) * Up) := by
        rw [show (Upi * ((y.1.2.unop : GLp p) : MP p) * Up) * (Upi * ((x.1.2.unop : GLp p) : MP p) * Up) =
          Upi * ((y.1.2.unop : GLp p) : MP p) * (Up * Upi) * ((x.1.2.unop : GLp p) : MP p) * Up by
            simp only [Matrix.mul_assoc], hU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      rw [e]; exact ZsVolGrp.intUp_mul _ hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    have hLL : Lp * Lpi = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hL
    have hUU : Upi * Up = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hU
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * (((x.1.1)⁻¹ : GLp p) : MP p) * Lpi)
      have hinv := ZsVolGrp.intLow_inv _ hx1
      have e : Lp * (((x.1.1)⁻¹ : GLp p) : MP p) * Lpi = (Lp * ((x.1.1 : GLp p) : MP p) * Lpi)⁻¹ := by
        symm
        apply Matrix.inv_eq_left_inv
        rw [show Lp * (((x.1.1)⁻¹ : GLp p) : MP p) * Lpi * (Lp * ((x.1.1 : GLp p) : MP p) * Lpi) =
          Lp * ((((x.1.1)⁻¹ : GLp p) : MP p) * (Lpi * Lp) * ((x.1.1 : GLp p) : MP p)) * Lpi by
            simp only [Matrix.mul_assoc], hL, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one, hLL]
      rw [e]; exact hinv.1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((((x.1.2)⁻¹).unop : GLp p) : MP p) * Up)
      rw [MulOpposite.unop_inv]
      have hinv := ZsVolGrp.intUp_inv _ hx2
      have e : Upi * (((x.1.2.unop)⁻¹ : GLp p) : MP p) * Up = (Upi * ((x.1.2.unop : GLp p) : MP p) * Up)⁻¹ := by
        symm
        apply Matrix.inv_eq_left_inv
        rw [show Upi * (((x.1.2.unop)⁻¹ : GLp p) : MP p) * Up * (Upi * ((x.1.2.unop : GLp p) : MP p) * Up) =
          Upi * ((((x.1.2.unop)⁻¹ : GLp p) : MP p) * (Up * Upi) * ((x.1.2.unop : GLp p) : MP p)) * Up by
            simp only [Matrix.mul_assoc], hU, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one, hUU]
      rw [e]; exact hinv.1

section PiP

theorem lOf_low {p : PlF D} (a b : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a) (hb : IsUpUni b) (i j : Fin (D.R.rS + 1))
    (hij : i < j) : lOf δ M p a b i j = 0 := by
  cases h : (M p).split with
  | none => simp only [lOf, h, lL, Matrix.of_apply, (ha i j).1 hij, map_zero, mul_zero, zero_mul]
  | some g =>
    simp only [lOf, h, lG, Matrix.of_apply, (ha i j).1 hij, (hb j i).1 hij]
    simp

theorem ρOf_up {p : PlF D} (a b : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a) (hb : IsUpUni b) (i j : Fin (D.R.rS + 1))
    (hij : j < i) : ρOf δ M p a b i j = 0 := by
  cases h : (M p).split with
  | none => simp only [ρOf, h, ρL, Matrix.of_apply, (hb i j).1 hij]; simp
  | some g =>
    simp only [ρOf, h, ρG, Matrix.of_apply, (hb i j).1 hij, (ha j i).1 hij]
    simp

theorem lOf_loUni {p : PlF D} (hA : Agree δ M p) (a b : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a) (hb : IsUpUni b) :
    IsLoUni (lOf δ M p a b) := fun i j =>
  ⟨fun h => lOf_low M δ a b ha hb i j h, fun h => by subst h; exact lOf_diag δ M hA a b ha hb i⟩

theorem ρOf_upUni {p : PlF D} (hA : Agree δ M p) (a b : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a) (hb : IsUpUni b) :
    IsUpUni (ρOf δ M p a b) := fun i j =>
  ⟨fun h => ρOf_up M δ a b ha hb i j h, fun h => by subst h; exact ρOf_diag δ M hA a b ha hb i⟩

theorem bOf_spec (β : VolPinAsm.StG w) : IsLoUni ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) ∧
    IsUpUni (VolPinAsm.bOf w β) ∧
    ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w * VolPinAsm.bOf w β = ptMat w := by
  obtain ⟨ha, b, hb, hW⟩ := β.2
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  have e : VolPinAsm.bOf w β = b := by
    unfold VolPinAsm.bOf
    have h1 : ((((β : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
        ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (ptMat w)⁻¹ * ((((β : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w
        = (ptMat w)⁻¹ * ((((β : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
            (((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b) := by rw [hW]
      _ = (ptMat w)⁻¹ * (((((β : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
            ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)) * ptMat w * b := by simp only [Matrix.mul_assoc]
      _ = b := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul]
  rw [e]
  exact ⟨ha, hb, hW⟩

theorem bOf_mul (β β' : Formalism.L2.SG.PairVal.GLR D) :
    VolPinAsm.bOf w (β * β') = VolPinAsm.bOf w β' * VolPinAsm.bOf w β := by
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  unfold VolPinAsm.bOf
  rw [mul_inv_rev, Units.val_mul]
  calc (ptMat w)⁻¹ * (((β'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
        ((β⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)) * ptMat w
      = (ptMat w)⁻¹ * ((β'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * (ptMat w * (ptMat w)⁻¹) *
          ((β⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w := by
        rw [Matrix.mul_nonsing_inv _ hWu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem bOf_one : VolPinAsm.bOf w (1 : Formalism.L2.SG.PairVal.GLR D) = 1 := by
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  unfold VolPinAsm.bOf
  rw [inv_one, Units.val_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hWu]

variable {p : PlF D} (hA : Agree δ M p)

def lU (β : Formalism.L2.SG.PairVal.GLR D) : GLp p :=
  ⟨lOf δ M p β (VolPinAsm.bOf w β), lOf δ M p (β⁻¹ : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w β⁻¹),
    by rw [← lOf_mul δ M hA, ← Units.val_mul, ← bOf_mul]
       simp only [mul_inv_cancel, inv_mul_cancel, Units.val_one, bOf_one]; exact lOf_one δ M hA,
    by rw [← lOf_mul δ M hA, ← Units.val_mul, ← bOf_mul]
       simp only [mul_inv_cancel, inv_mul_cancel, Units.val_one, bOf_one]; exact lOf_one δ M hA⟩

def ρU (β : Formalism.L2.SG.PairVal.GLR D) : GLp p :=
  ⟨ρOf δ M p β (VolPinAsm.bOf w β), ρOf δ M p (β⁻¹ : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w β⁻¹),
    by rw [← ρOf_mul δ M hA, ← Units.val_mul, ← bOf_mul]
       simp only [mul_inv_cancel, inv_mul_cancel, Units.val_one, bOf_one]; exact ρOf_one δ M hA,
    by rw [← ρOf_mul δ M hA, ← Units.val_mul, ← bOf_mul]
       simp only [mul_inv_cancel, inv_mul_cancel, Units.val_one, bOf_one]; exact ρOf_one δ M hA⟩

def πP : VolPinAsm.StG w →* StP M δ u u' w p where
  toFun β := ⟨(lU M δ w hA β, MulOpposite.op (ρU M δ w hA β)), by
    obtain ⟨ha, hb, hW⟩ := bOf_spec w β
    refine ⟨lOf_loUni M δ hA _ _ ha hb, ρOf_upUni M δ hA _ _ ha hb, ?_⟩
    show lOf δ M p ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β) * Y0 M δ u u' w p *
      ρOf δ M p ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β) = Y0 M δ u u' w p
    unfold Y0
    rw [← move δ M u u' hA _ _ ha hb, ZsVolGrp.zhatOM_zhatOM, hW]⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      show lOf δ M p ((1 : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w ((1 : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D)) = 1
      rw [OneMemClass.coe_one, bOf_one, Units.val_one, lOf_one δ M hA]
    · apply MulOpposite.unop_injective
      apply Units.ext
      show ρOf δ M p ((1 : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w ((1 : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D)) = 1
      rw [OneMemClass.coe_one, bOf_one, Units.val_one, ρOf_one δ M hA]
  map_mul' β β' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      show lOf δ M p ((β * β' : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w ((β * β' : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D)) =
        lOf δ M p ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β) *
          lOf δ M p ((β' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β')
      rw [Subgroup.coe_mul, bOf_mul, Units.val_mul, lOf_mul δ M hA]
    · apply MulOpposite.unop_injective
      apply Units.ext
      show ρOf δ M p ((β * β' : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w ((β * β' : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D)) =
        ρOf δ M p ((β' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β') *
          ρOf δ M p ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β)
      rw [Subgroup.coe_mul, bOf_mul, Units.val_mul, ρOf_mul δ M hA]

end PiP

section Props

open Formalism.L2.SG.Pf.ZsVolCut

variable {p : PlF D}

theorem lp_inv (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U = 1 := by
  rw [← lOf_mul δ M hA, (ZsVolGrp.isLoUni_inv hL).2.1, (ZsVolGrp.isUpUni_inv hU).2.2, lOf_one δ M hA]

theorem up_inv (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹ = 1 := by
  rw [← ρOf_mul δ M hA, (ZsVolGrp.isLoUni_inv hL).2.1, (ZsVolGrp.isUpUni_inv hU).2.2, ρOf_one δ M hA]

def CPL (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) : Subgroup (StP M δ u u' w p) :=
  CP M δ u u' w p (lOf δ M p L U) (lOf δ M p L⁻¹ U⁻¹) (ρOf δ M p L U) (ρOf δ M p L⁻¹ U⁻¹)
    (lp_inv M δ hA L U hL hU) (up_inv M δ hA L U hL hU)

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def ApproxC : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : HypE M δ u u' F0 what₂ γ w F' L U),
    ∃ S : Finset (PlF D),
      (∀ p ∉ S, AP M δ u u' w p = CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1) ∧
      (∀ p, (CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1).relIndex (AP M δ u u' w p) ≠ 0 ∧
        (AP M δ u u' w p).relIndex (CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1) ≠ 0) ∧
      ∀ h : ∀ p, StP M δ u u' w p, ∃ g : VolPinAsm.StG w,
        (∀ p ∈ S, (h p)⁻¹ * πP M δ u u' w (hE.1 p) g ∈
          AP M δ u u' w p ⊓ CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1) ∧
        ∀ p ∉ S, πP M δ u u' w (hE.1 p) g ∈ AP M δ u u' w p

def LocIdxC : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (AP M δ u u' w p) (CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1) =
      Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)

end Props

end Formalism.L2.SG.Pf.ProdE
