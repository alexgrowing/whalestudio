import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepNewAE
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharpolySmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af

open GroundTheory.Automorphic in

theorem UpperTheory.V.Br.hermEx : Gk.HermEx :=
  Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) fun F _ _ _ a => by
    refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ => congrArg Subtype.val (CuspFin.uAction_lieEq X φ)⟩
    rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
    rfl
