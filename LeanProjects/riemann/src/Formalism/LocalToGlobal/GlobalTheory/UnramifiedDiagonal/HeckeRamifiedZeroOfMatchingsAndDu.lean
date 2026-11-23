import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.TrpDia
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.UpMatch
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnDiaMatch0FHolds

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

variable {D : D7} {u : D.what₂.Word}

theorem hecke_ramified_zero_of_same_place (T : Forms0 D u) (hU : UpDiaSame0F T) (hD : DnDiaSame0F T) (hE : EDiaSame0F T)
    (h6 : DUFormulaLevelZero D u) : HeckeRamifiedLevelZero D u :=
  hecke_ramified_zero_of_matchings T (CrossDiaZero.upMatch T) (CrossDiaZero.dnMatchAll_holds D u T) (diamond_same_place_of_matchings T hU hD)
    (trpDia0_of T hU hE) h6

def SameAll : Prop := ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), UpDiaSame0F T ∧ DnDiaSame0F T ∧ EDiaSame0F T

def UpSameAll : Prop := ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), UpDiaSame0F T

def DnSameAll : Prop := ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), DnDiaSame0F T

def ESameAll : Prop := ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), EDiaSame0F T

def DUAll : Prop := ∀ (D : D7) (u : D.what₂.Word), Forms0 D u → DUFormulaLevelZero D u

theorem hecke_ramified_zero_of_matchings_and_du (hS : SameAll) (h6 : DUAll) :
    ∀ (D : D7) (u : D.what₂.Word), HidaSetting D u → RT.ConcreteFormsLevelZero D u → HeckeRamifiedLevelZero D u := by
  intro D u hs ht
  obtain ⟨hf, -⟩ := ht
  obtain ⟨Ch, chOf, T, -⟩ := hf
  let F : Forms0 D u :=
    { atT := T.atT
      cls0 := T.cls 0 (Nat.zero_le _) (Or.inl rfl)
      val0 := T.val 0 (Nat.zero_le _) (Or.inl rfl)
      gl := T.gl
      gl_K := T.gl_K
      glev0 := T.glev0
      lv0 := T.lv 0 (Nat.zero_le _)
      fMe0 := T.fMe 0 (Nat.zero_le _) (Or.inl rfl)
      fv0 := T.fv 0 (Nat.zero_le _) (Or.inl rfl)
      up_natural_level_zero := T.upN 0 (Nat.zero_le _) (Or.inl rfl)
      down_natural_level_zero := T.dnN 0 (Nat.zero_le _) (Or.inl rfl)
      norm0 := T.norm 0 (Nat.zero_le _) (Or.inl rfl)
      bw0 := T.bw 0 (Nat.zero_le _) (Or.inl rfl) }
  obtain ⟨hU, hD, hE⟩ := hS D u F
  exact hecke_ramified_zero_of_same_place F hU hD hE (h6 D u F)

end Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

end
