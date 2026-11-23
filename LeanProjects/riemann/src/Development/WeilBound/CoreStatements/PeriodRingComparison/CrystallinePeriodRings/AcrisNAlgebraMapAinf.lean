import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow

noncomputable section
open GroundTheory.PAdicHodge
namespace Cmp6
variable (l : ℕ) [Fact l.Prime]

theorem tiltMap_eq : Reformulated.AutPerF.Tilt.map l (e l).toRingHom = Formalism.Per6.tiltMap l := by
  refine RingHom.ext fun x => Reformulated.AutPerF.Tilt.ext fun n => ?_
  rw [Reformulated.AutPerF.Tilt.coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  change _ = Formalism.Per6.modPEquiv l (PreTilt.coeff n x)
  rw [← ha, Ideal.quotientMap_mk]
  rfl

theorem ainfMap_eq : Reformulated.AutPerF.Ainf.map l (e l).toRingHom = Formalism.Per6.ainfMap l := by
  rw [Reformulated.AutPerF.Ainf.map, tiltMap_eq]
  rfl

theorem acrisNHom_algebraMap (y : Reformulated.AutPerF.AcrisZero l (NC l)) :
    acrisNHom l (algebraMap _ (Reformulated.AutPerF.Acris l (NC l)) y) =
      algebraMap (ACris.ACrisZero ℂ_[l] l) (ACris.ACris ℂ_[l] l) (zeroEquiv l y) :=
  Reformulated.AutPerF.adicMap_algebraMap _ _ _ _ y

theorem zeroEquiv_algebraMap (a : Reformulated.AutPerF.Ainf l (NC l)) :
    zeroEquiv l (algebraMap _ (Reformulated.AutPerF.AcrisZero l (NC l)) a) =
      algebraMap (AInf ℂ_[l] l) (ACris.ACrisZero ℂ_[l] l) a := rfl

theorem acrisN_algebraMap_ainf (a : Reformulated.AutPerF.Ainf l (NC l)) :
    acrisN l (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.Acris l (NC l)) a) =
      algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) a := by
  rw [IsScalarTower.algebraMap_apply (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AcrisZero l (NC l))
    (Reformulated.AutPerF.Acris l (NC l))]
  change acrisNHom l _ = _
  rw [acrisNHom_algebraMap, zeroEquiv_algebraMap,
    IsScalarTower.algebraMap_apply (AInf ℂ_[l] l) (ACris.ACrisZero ℂ_[l] l) (ACris.ACris ℂ_[l] l)]

theorem cA_algebraMap (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a) =
      algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Formalism.Per6.ainfMap l a) := by
  rw [cA_apply, Reformulated.AutPerF.Acris.map_algebraMap, ainfMap_eq]
  exact acrisN_algebraMap_ainf l _

end Cmp6
