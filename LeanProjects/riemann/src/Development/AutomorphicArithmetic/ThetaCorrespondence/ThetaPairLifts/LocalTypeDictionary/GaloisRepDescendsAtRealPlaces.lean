import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroOfHoweUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NonGaloisDownLiftNonvanishing
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroOfHoweUnramifiedStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host
namespace GlobalTheory.DownLift.AtReal
theorem lift_splits_locally : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ (D : D7) (cf : CharFrame D)
    (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  intro hP hH hX D cf nch tp X j t
  have hR : GlobalTheory.RawLift.RallisConv D := GlobalTheory.RawLift.Assembled.rallisConv_of_siegelWeil hP hX.sw D
  have hN : ∀ i t, GlobalTheory.DownLift.NonVan X.R i t := fun i t =>
    _root_.GlobalTheory.T.nonGalois_downLift_nonvanishing hP hX.dbl hX.udbl hX.hl hH D X.G X.Pl0 X.T X.A X.Ks X.R X.F X.given X.full i t
  exact ((GlobalTheory.T.liftInj_and_properties_of_rallis_of_nonVan hP hH D X.G X.Pl0 X.T X.A X.Ks X.R X.F X.given X.full hR hN).2 j t).1
end GlobalTheory.DownLift.AtReal
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRep_descends_at_real_places : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  first | exact @_root_.GlobalTheory.DownLift.AtReal.lift_splits_locally | exact _root_.GlobalTheory.DownLift.AtReal.lift_splits_locally | (intros; apply _root_.GlobalTheory.DownLift.AtReal.lift_splits_locally <;> assumption)
end
