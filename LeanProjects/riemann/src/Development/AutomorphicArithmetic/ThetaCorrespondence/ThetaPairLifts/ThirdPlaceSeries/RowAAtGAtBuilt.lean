import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowAAtGAtBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
namespace GlobalTheory.Fc
theorem row_aAtG_at_built_alt (𝒮 : Slots) (hR : 𝒮.Rx = RX) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) :
    Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.ArithmeticConditionAtBundlePoints S Lk := by
  refine ⟨fun _ _ _ _ _ => True, largeBaseProperty_true, ?_⟩
  refine GlobalTheory.T.holds_at_bundlePoints_of_trueColumns _ Lk fun K X f T c h => ?_
  refine positionOf_mono (P := GoodE 𝒮) ?_ K X f T c h.1
  rintro K B f T w Z c ⟨⟨b, -⟩, -⟩
  refine ⟨(GlobalTheory.Svd.builtC_hasPart 𝒮).1 K B f T w Z c ⟨b⟩, fun a => ?_⟩
  have hx : RX K B f T w Z c.Wt c.O.p0 b.what₂ := hR ▸ b.rx
  exact GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties K B f T w Z c.Wt c.O.p0 b.what₂ hx a
end GlobalTheory.Fc
end
