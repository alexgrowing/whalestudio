import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.JointWinOfCounts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PropZ
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoTwCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaKOfPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.KBridgeOfKPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.MainCotSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Mprime
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CongruenceNumberRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CountVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Number
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ConductorAtMapInjectiveCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CongNum
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ChrInvNeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LemmaX
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ResidualBernoulliNonvanishing
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UnitaryLiftTheoremOfReducedForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Xpp
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoHostVanE

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.HV.U

theorem pt (hN : LitN) : GlobalTheory.Published.PoitouTateDuality := GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hN.coh.pt

theorem lemmaK (hN : LitN) (hK : K.KBridge) : ∃ CK : ℝ, LemmaK CK :=
  (K.lemmaK (pt hN) hN.coh.lfK hN.coh.ltK hK).imp fun _ h => h.2

theorem localGaloisCohomology₂ (hN : LitN) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩

theorem hostVanE (hN : LitN) (hK : K.KBridge) : UnitaryThreeInertia.HostVanE := by
  obtain ⟨CK, hL⟩ := lemmaK hN hK
  exact X.So.hostVanE CK hL (pt hN) hN.coh.lfK hN.coh.ltK hN.coh.lf hN.coh.lt hN.coh.le

end UpperTheory.V.HV.U
