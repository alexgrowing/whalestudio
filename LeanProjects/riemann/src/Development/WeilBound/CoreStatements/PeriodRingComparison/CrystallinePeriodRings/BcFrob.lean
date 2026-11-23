import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisPlusHomAlgebraMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem bcris_hom_ext_acris {B : Type} [CommRing B] {f g : Reformulated.AutPerF.Bcris l (OC l) →+* B}
    (h : ∀ x : Reformulated.AutPerF.Acris l (OC l),
      f (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)) x) =
        g (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)) x)) : f = g := by
  apply Reformulated.AutPerF.Bcris.hom_ext
  intro z
  have h2 : f.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) =
      g.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) := by
    apply Reformulated.AutPerF.BcrisPlus.hom_ext
    intro y
    exact h y
  exact RingHom.congr_fun h2 z

theorem cBc_frob_of
    (hφ : ∀ x, cA l (Reformulated.AutPerF.Acris.frob l (OC l) x) = ACris.phi ℂ_[l] l (cA l x))
    (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) b) = Formalism.Per6.φB l (cBc l b) := by
  have h : (cBc l).toRingHom.comp (Reformulated.AutPerF.Bcris.frob l (OC l)) =
      (Formalism.Per6.φB l).comp (cBc l).toRingHom :=
    bcris_hom_ext_acris l fun x => by
      change cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) _) = Formalism.Per6.φB l (cBc l _)
      rw [Reformulated.AutPerF.Bcris.frob_algebraMap_acris, cBc_algebraMap, cBc_algebraMap, hφ,
        PositivityTheory.LocInh.φB_cB]
  exact RingHom.congr_fun h b

theorem cBc_aB (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cBc l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a)) =
      Formalism.Per6.aB l a := by
  rw [cBc_algebraMap, cA_algebraMap]
  exact (PositivityTheory.LocInh.frob_aB_apply a).symm

theorem algebraMap_ainf_eq_zA (z : ℤ_[l]) :
    algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z = Formalism.Per6.zA l z := rfl

theorem cBc_zB (z : ℤ_[l]) :
    cBc l (algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zB l z := by
  have h : algebraMap ℤ_[l] (Reformulated.AutPerF.Acris l (OC l)) z =
      algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l))
        (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z) := rfl
  rw [Reformulated.AutPerF.Bcris.algebraMap_padicInt, h, cBc_aB, algebraMap_ainf_eq_zA, Formalism.Per6.zB,
    RingHom.comp_apply]

end Cmp6
