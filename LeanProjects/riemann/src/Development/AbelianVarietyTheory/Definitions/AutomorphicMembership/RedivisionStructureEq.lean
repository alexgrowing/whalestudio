import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure New (D : D7) : Type 1 where
  Z : SNew D
  N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V
  h : D.what₂.Word → ℝ

def reD (D : D7) (Z : New D) : D7 := GlobalTheory.EX.OB.setDiv (reS D Z.Z) Z.N Z.h

set_option maxHeartbeats 4000000 in

def SameForms0LevelsAndValues {D : D7} (Z : New D) (F : ∀ u, Forms0 D u) (F' : ∀ u, Forms0 (reD D Z) u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev = (F u).cls0.lev ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY

variable {D : D7} (Z : New D)

def wd (u : D.what₂.Word) : (reD D Z).what₂.Word := u

def New.self (D : D7) : New D := ⟨SNew.self D, fun u => (D.div.Nu u).L, D.div.h⟩

def New.ofDiv (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : New D := ⟨SNew.self D, N, h⟩

instance instInhabitedNew (D : D7) : Inhabited (New D) := ⟨New.self D⟩

theorem reD_ofDiv (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) :
    reD D (New.ofDiv D N h) = GlobalTheory.EX.OB.setDiv D N h := rfl

theorem reD_rows : (reD D Z).what₂ = D.what₂ := rfl

theorem reD_host : (reD D Z).host = D.host := rfl

theorem redivision_structure_eq : (reD D Z).s = mix D.s Z.Z.s := rfl

theorem reD_atP : (reD D Z).s.atP = D.s.atP := rfl

theorem reD_HH : (reD D Z).s.HH = Z.Z.s.HH := rfl

theorem reD_h : (reD D Z).div.h = Z.h := rfl

theorem reD_L (u : D.what₂.Word) : ((reD D Z).div.Nu u).L = Z.N u := rfl

example (D : D7) (u : D.what₂.Word) : (reD D (New.ofDiv D (fun _ => ⊥) fun _ => 1)).div.h u = 1 := rfl

example (D : D7) : (reD D (New.self D)).s = D.s := rfl

set_option maxHeartbeats 4000000 in

def reX (X : HidaSetting D) : HidaSetting (reD D Z) := { X with }

end GlobalTheory.Mem.SRe

end
