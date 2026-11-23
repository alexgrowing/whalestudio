import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pt_realised {D : D7} {O : Obj D} {c : ℝ} (b : Part D O c) : b.pt.Realised :=
  ⟨b.R, b.S, b.B, b.pins, b.Rr, b.recPins, rfl⟩

theorem pt_pb {D : D7} {O : Obj D} {c : ℝ} (b : Part D O c) : b.pt.T.pb = b.pt.R.C.P.pb :=
  GlobalTheory.PinsFixHalf.pb_eq_of_pins b.pt.T b.pt.R.toRealDat b.pt.κ b.pt.v₀ b.pt.O b.pt.charW.base.lev b.pt.fw.laws b.pt.pins

theorem pt_ties0 : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Part D O c), b.pt.Realised ∧ b.pt.T.pb = b.pt.R.C.P.pb :=
  fun _ _ _ b => ⟨pt_realised b, pt_pb b⟩

end GlobalTheory.Fc.Ind

example : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Ind.Part D O c), b.pt.Realised ∧ b.pt.T.pb = b.pt.R.C.P.pb := GlobalTheory.Fc.Ind.pt_ties0
