import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioMap

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

theorem loUni_of_int {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) : IsLoUni l :=
  fun i j => ⟨h.2.1 i j, fun e => e ▸ h.1 i⟩

theorem upUni_of_int {l : MP p} (h : Formalism.MainNotions.S.TieN.IntUp (M p) l) : IsUpUni l :=
  fun i j => ⟨h.2.1 i j, fun e => e ▸ h.1 i⟩

section
variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)

theorem conj_first_factor (x : GG p) :
    (((g0 M δ hA L U hL hU * x * (g0 M δ hA L U hL hU)⁻¹).1 : GLp p) : MP p) =
      lOf δ M p L U * ((x.1 : GLp p) : MP p) * lOf δ M p L⁻¹ U⁻¹ := by
  simp only [g0, Prod.fst_mul, Prod.fst_inv, Units.val_mul, Units.inv_mk]

theorem conj_second_factor (x : GG p) :
    ((((g0 M δ hA L U hL hU * x * (g0 M δ hA L U hL hU)⁻¹).2).unop : GLp p) : MP p) =
      ρOf δ M p L⁻¹ U⁻¹ * ((x.2.unop : GLp p) : MP p) * ρOf δ M p L U := by
  simp only [g0, Prod.snd_mul, Prod.snd_inv, MulOpposite.unop_mul, MulOpposite.unop_inv, MulOpposite.unop_op,
    Units.val_mul, Units.inv_mk]
  rw [Matrix.mul_assoc]

theorem cShape (w : Point D.host.E (D.R.rS + 1)) : CShapeAt M δ u u' w hA L U hL hU := by
  have hLL : lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U = 1 := lp_inv M δ hA L U hL hU
  have hLL' : lOf δ M p L U * lOf δ M p L⁻¹ U⁻¹ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hLL
  have hUU : ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹ = 1 := up_inv M δ hA L U hL hU
  have hUU' : ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p L U = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hUU
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  set Y := Y0 M δ u u' w p
  have key : ∀ a b : MP p, (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * (a * Y * b) * Up := by
    intro a b
    calc (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * a * (Lpi * Lp) * Y * (Up * Upi) * b * Up := by
          simp only [Matrix.mul_assoc]
      _ = Lp * (a * Y * b) * Up := by rw [hLL, hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  ext x
  rw [mem_cj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨_, _, hy3⟩ := y.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) _
      rw [conj_first_factor]; exact hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) _
      rw [conj_second_factor]; exact hy2
    · show _ * XP M δ u u' w L U * _ = XP M δ u u' w L U
      rw [conj_first_factor, conj_second_factor]
      show (Lp * _ * Lpi) * (Lp * Y * Up) * (Upi * _ * Up) = Lp * Y * Up
      rw [key]
      exact congrArg (fun z => Lp * z * Up) hy3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h1' : Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1 : GLp p) : MP p) * Lpi) := by
      have := h1; rw [show Formalism.MainNotions.S.TieN.IntLow (M p) _ = _ from rfl, conj_first_factor] at this; exact this
    have h2' : Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((x.2.unop : GLp p) : MP p) * Up) := by
      have := h2; rw [show Formalism.MainNotions.S.TieN.IntUp (M p) _ = _ from rfl, conj_second_factor] at this; exact this
    have h3' : (Lp * ((x.1 : GLp p) : MP p) * Lpi) * (Lp * Y * Up) * (Upi * ((x.2.unop : GLp p) : MP p) * Up) =
        Lp * Y * Up := by
      have := h3
      change _ * XP M δ u u' w L U * _ = XP M δ u u' w L U at this
      rw [conj_first_factor, conj_second_factor] at this
      exact this
    rw [key] at h3'
    have hst : ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p) = Y := by
      have := congrArg (fun z => Lpi * z * Upi) h3'
      calc ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)
          = (Lpi * Lp) * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * (Up * Upi) := by
            rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
        _ = Lpi * (Lp * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * Up) * Upi := by
            simp only [Matrix.mul_assoc]
        _ = Lpi * (Lp * Y * Up) * Upi := this
        _ = Y := by
            calc Lpi * (Lp * Y * Up) * Upi = (Lpi * Lp) * Y * (Up * Upi) := by simp only [Matrix.mul_assoc]
              _ = Y := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
    have hlo : IsLoUni ((x.1 : GLp p) : MP p) := by
      have e : ((x.1 : GLp p) : MP p) = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by
        calc ((x.1 : GLp p) : MP p) = (Lpi * Lp) * ((x.1 : GLp p) : MP p) * (Lpi * Lp) := by
              rw [hLL, Matrix.one_mul, Matrix.mul_one]
          _ = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by simp only [Matrix.mul_assoc]
      rw [e]
      exact ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul
        (lOf_loUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1) (loUni_of_int M h1'))
        (lOf_loUni M δ hA _ _ hL hU)
    have hup : IsUpUni ((x.2.unop : GLp p) : MP p) := by
      have e : ((x.2.unop : GLp p) : MP p) = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by
        calc ((x.2.unop : GLp p) : MP p) = (Up * Upi) * ((x.2.unop : GLp p) : MP p) * (Up * Upi) := by
              rw [hUU, Matrix.one_mul, Matrix.mul_one]
          _ = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by simp only [Matrix.mul_assoc]
      rw [e]
      exact ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul (ρOf_upUni M δ hA _ _ hL hU) (upUni_of_int M h2'))
        (ρOf_upUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1)
    exact ⟨⟨x, hlo, hup, hst⟩, ⟨h1', h2'⟩, rfl⟩

end

end Formalism.L2.SG.Pf.ProdEP2Cut
