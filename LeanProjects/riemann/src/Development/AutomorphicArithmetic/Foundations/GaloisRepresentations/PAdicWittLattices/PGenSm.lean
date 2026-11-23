import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pGenSm : GenSm := by
  intro p _ D R _ _ gb N X
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R (GenCmp.baseOf gb) N.1 N.2.1 N.2.2
  obtain ⟨j, hoi, hci, hj, -⟩ := GenCmp.genModel_eq_genericFibre p D R (GenCmp.baseOf gb) R (RingHom.id R) gb
    rfl (fun _ => rfl) N.1 N.2.1 N.2.2 M X
  haveI := hoi
  haveI := hci
  haveI : IsQProjOver M.s := M.qproj
  haveI : SmoothOfRelativeDimension (D.a * (D.n - 1)) M.s := M.smooth
  haveI : IsSeparated M.s := GlobalTheory.ZM.isSeparated_of_isQProjOver M.qproj
  haveI : QuasiCompact M.s := quasiCompact_of_qProj M.qproj
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  rw [← hj]
  refine ⟨inferInstance, inferInstance, inferInstance, fun hB => ?_⟩
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd (RingHom.id R)
      (Model.isProjOver_of_compactB p D R (GenCmp.baseOf gb) N.1 N.2.1 N.2.2 hB M))
