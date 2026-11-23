import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BuiltCHasPart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeliveryAtBundlePointsOfTrueColumnsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherPropertiesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem row_aAtG_at_built (𝒮 : Slots) (hR : 𝒮.Rx = RX) (Lk : LkT Bundle) :
    Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.ArithmeticConditionAtBundlePoints S Lk := by
  refine ⟨fun _ _ _ _ _ => True, largeBaseProperty_true, ?_⟩
  refine GlobalTheory.T.holds_at_bundlePoints_of_trueColumns _ Lk fun K X f T c h => ?_
  refine positionOf_mono (P := GoodE 𝒮) ?_ K X f T c h.1
  rintro K B f T w Z c ⟨⟨b, -⟩, -⟩
  refine ⟨(GlobalTheory.Svd.builtC_hasPart 𝒮).1 K B f T w Z c ⟨b⟩, fun a => ?_⟩
  have hx : RX K B f T w Z c.Wt c.O.p0 b.what₂ := hR ▸ b.rx
  exact GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties K B f T w Z c.Wt c.O.p0 b.what₂ hx a

end GlobalTheory.Fc
