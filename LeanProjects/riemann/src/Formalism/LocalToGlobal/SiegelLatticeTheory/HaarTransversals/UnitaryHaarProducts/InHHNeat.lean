import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def NeatKu (hK : X.LevelSubgroupCharacter) : Prop := Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK)

def GamFinKu (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (h : Hfin X u) (γ : Gam X u), h⁻¹ * iotaF X u γ * h ∈ Ku X u hK → IsOfFinOrder γ

def GamUnipKu (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (h : Hfin X u) (γ : Gam X u), h⁻¹ * iotaF X u γ * h ∈ Ku X u hK → IsOfFinOrder γ → γ = 1

theorem cols_dim_of_neat (hK : X.LevelSubgroupCharacter) (hN : NeatKu X u hK) (hC : ClassFin X u hK) :
    FiniteDimensional ℂ (Cu X u hK) ∧
      Module.finrank ℂ (Cu X u hK) =
        Module.finrank ℂ (X.Vpi u) * Nat.card (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK)) := by
  exact Formalism.L2.SG.ColsDim.columns_dimension _ _ _ ℂ (X.Vpi u) (iotaI X u) (iotaF X u) (Ku X u hK) (Ku X u hK)
    (psiK X u hK) (piRep X u) le_rfl hN hC inferInstance

end Formalism.L2.SG.PoincareInHH.Cut
