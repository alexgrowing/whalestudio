import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.UptsExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdTEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdQEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdTensor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MuHomSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MuAlgebraMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMuStar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PJSurj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLatCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PVecCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PEvEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TraceMapUnipotent
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ValLeOneOfForall
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPIntRev
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIntConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIntCof

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc comp rat mat)

namespace UpperTheory.Gal.W2.Seed

theorem isoEx'_holds : IsoEx' := fun E _ _ _ A n hn => by
  obtain ⟨a, h1, h2⟩ := UpperTheory.Gal.G1.IsoEx_holds E A n hn
  refine ⟨a, ?_, h2⟩
  rw [Matrix.diagonal_map (map_zero _)] at h1
  exact h1

theorem adTEx_holds : AdTEx := pAdTEx pAdQEx pAdTensor pIdemP

theorem trEx_holds : TrEx := pTrEx adTEx_holds pMuEx isoEx'_holds (pJEx pMuStar) pJEq (pJSurj pIdemP pMuStar)

theorem latCoord_holds : LatCoord := pLatCoord pRepLaws

theorem vecCoord_holds : VecCoord := pVecCoord latCoord_holds pEvEx

end UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.Int.Geo.Pl

open UpperTheory.Gal.W2.Seed

theorem intCof_holds : UpperTheory.Gal.Int.Geo.Pl.IntCof := fun E _ _ _ n g => pIntCof E n (mat g)

theorem frameEx_holds : FrameEx := fun E _ _ _ A n p _ S hn => by
  obtain ⟨T⟩ := trEx_holds E A n p S hn
  obtain ⟨vec, v1, v2, v3, v4, v5, v6⟩ := vecCoord_holds E A n p S T
  obtain ⟨B, x, hx, hm, he⟩ := pStdForm2 pMuStar E A n p S T
  exact ⟨{
    j := T.j
    surj := fun h => ⟨T.sec h, T.j_sec h⟩
    ker := fun g => by simpa using T.j_eq g 1
    a := fun w => GeneralLinearGroup.map (pLoc E w) T.a
    a_int := T.iso.2
    a_cof := pIntCof E n T.a
    vec := vec
    vec_inj := v1
    vec_hat := v2
    vec_surj := v3
    vec_in := v4
    vec_act := v5
    vec_mul := v6
    ρ := T.ρ
    ρ_int := T.int
    mult := T.j_sim
    B := B
    x := x
    t := 1
    hx := hx
    mem := hm
    emb1 := he
    emb2 := fun y _ h' => ⟨fun h => (pPInt E A n p S ⟨y, h'⟩ h).1, fun h => pPIntRev pIntConj E A n p S ⟨y, h'⟩ h⟩
    th := CertificateRingHomMap.th
    th_mat := fun _ => rfl
    th_sim := fun _ => rfl
    tr := T
    j_tr := rfl
    a_tr := fun _ => rfl }⟩

end UpperTheory.Gal.Int.Geo.Pl
