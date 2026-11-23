import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLawsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Chr

def trueDtPack {R : Ranks} {H : Formalism.BasicNotions.Host R} {e : Fin R.m → R.Psi → ℚ} (C : HFrame H e) : DtPack H :=
  letI := H.cmStar
  { Dt := DtT H
    instDt := inferInstance
    muTil := muTilT H C.mu0
    chiD := tildeD H C.chiPsi
    UO := UOT H
    chiD_UO := (GlobalTheory.T.tilde_character_on_unitary R H C.chiPsi C.isChi).1
    e1Dt := e1T H
    rest_detCharacter_on_unitary_eq := (GlobalTheory.T.tilde_character_on_unitary R H C.chiPsi C.isChi).2
    relDet := fun N L L' => relDetT H N L.1 L'.1
    relDet_self := fun N => (GlobalTheory.T.relativeLatticeDeterminantClass_laws R H N).1
    relDet_mul := fun N => (GlobalTheory.T.relativeLatticeDeterminantClass_laws R H N).2.1
    relDet_smul := fun N => (GlobalTheory.T.relativeLatticeDeterminantClass_laws R H N).2.2 }

end GlobalTheory.Mem.Chr
