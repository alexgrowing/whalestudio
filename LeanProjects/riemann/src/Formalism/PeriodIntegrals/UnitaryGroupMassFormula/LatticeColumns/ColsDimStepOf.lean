import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Development

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH

def NeatKuStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter),
    Formalism.L2.SG.ColsDim.StabTriv (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)

def ClassFinStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter),
    Finite (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK))

def ClassCountStep' : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    AdBridgeGF X.B.I → X.MeasTie hb → X.LevelSubgroupNormalized →
    Formalism.L2.SG.ColsDim.StabTriv (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK) →
    Finite (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)) →
    (Nat.card (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)) : ℝ) =
      covol (X.measW u).μH /
        ((X.muH u Set.univ).toReal * ((X.measW u).μHf (Subtype.val ⁻¹' K2u X hb u)).toReal)

theorem colsDimStep_of' (hGF : ∀ I : Formalism.MainNotions.S.AutInst, AdBridgeGF I) (hN : NeatKuStep) (hF : ClassFinStep)
    (hC : ClassCountStep') : ColsDimStep := by
  intro D X hb hK u hMT hL
  have hS := hN X u hK
  have hFin := hF X u hK
  have hcount := hC X hb hK u (hGF _) hMT hL hS hFin
  have hdim := (Formalism.L2.SG.ColsDim.columns_dimension _ _ _ ℂ _ (PoincareSetting.iotaI X u) (PoincareSetting.iotaF X u)
    (PoincareSetting.Ku X u hK) (PoincareSetting.Ku X u hK) (PoincareSetting.psiK X u hK) (PoincareSetting.piRep X u) le_rfl hS hFin
    inferInstance).2
  have hdim' : Module.finrank ℂ (PoincareSetting.Cu X u hK) = Module.finrank ℂ (X.Vpi u) *
      Nat.card (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)) := hdim
  rw [hdim', Nat.cast_mul, hcount]

end PIW.MassDataColumns
