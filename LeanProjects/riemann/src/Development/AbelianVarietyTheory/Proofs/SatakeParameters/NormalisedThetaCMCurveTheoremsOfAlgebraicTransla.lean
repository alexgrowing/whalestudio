import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodOrdinaryModelAtTwoCmLatticeSevenModEight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocJetsAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntSExpMulTranslate
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.ThLoc

theorem inputs_of_algT (hT : Formalism.L2.KerInert.AlgTAll) : Inputs where
  jInt := cm1
  modelTwo := goodOrdinaryModelAtTwo_cmLattice_seven_mod_eight
  jetsOdd := locJets_all.1
  jetsTwo := locJets_all.2.1
  jetsThree := thetaZJetsThree
  shape := locJets_all.2.2
  algT := hT
  lamExt := place_extends_to_iso

end GlobalTheory.ThLoc
