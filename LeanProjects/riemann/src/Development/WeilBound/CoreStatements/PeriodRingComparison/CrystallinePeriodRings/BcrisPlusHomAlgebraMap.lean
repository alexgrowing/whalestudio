import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.WeilBound.CoreStatements.PeriodRingComparison.PrimitiveEpsilon.UntiltEpsilonEqOne
import Development.WeilBound.CoreStatements.PeriodRingComparison.TeichmullerLogarithm.LogEps
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cA_symm_tA : (cA l).symm (Formalism.Per6.tA l) = Reformulated.AutPerF.Acris.logTeich (eps0 l) := by
  rw [← acris_log_teichmuller_epsilon, RingEquiv.symm_apply_apply]

theorem isUnit_bcris_l : IsUnit ((l : ℕ) : Formalism.Per6.Bcris l) := by
  simpa using PositivityTheory.LocInh.isUnit_cB_l l

def bcrisPlusHom : Reformulated.AutPerF.BcrisPlus l (OC l) →+* Formalism.Per6.Bcris l :=
  Reformulated.AutPerF.BcrisPlus.lift ((Formalism.Per6.cB l).comp (cA l).toRingHom) (isUnit_bcris_l l)

theorem bcrisPlusHom_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    bcrisPlusHom l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  Reformulated.AutPerF.BcrisPlus.lift_algebraMap _ _ x

theorem isUnit_cB_cA_logTeich {ε : Reformulated.AutPerF.tateModule l (OC l)} (hε : Reformulated.AutPerF.IsPrimitive ε) :
    IsUnit (Formalism.Per6.cB l (cA l (Reformulated.AutPerF.Acris.logTeich ε))) := by
  obtain ⟨a, rfl⟩ := (epsilon_isPrimitive l).exists_unit hε
  rw [Reformulated.AutPerF.Acris.logTeich_padicPow, ← cA_symm_tA, map_mul, RingEquiv.apply_symm_apply,
    map_mul]
  exact (((a.isUnit.map (algebraMap ℤ_[l] (Reformulated.AutPerF.Acris l (OC l)))).map (cA l)).map
    (Formalism.Per6.cB l)).mul (Formalism.Per6.Loc2.isUnit_right _ _)

def bcrisHom : Reformulated.AutPerF.Bcris l (OC l) →+* Formalism.Per6.Bcris l :=
  Reformulated.AutPerF.Bcris.lift (bcrisPlusHom l) (fun ε hε => by
    rw [bcrisPlusHom_algebraMap]
    exact isUnit_cB_cA_logTeich l hε)

theorem bcrisHom_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    bcrisHom l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  (Reformulated.AutPerF.Bcris.lift_algebraMap _ _ _).trans (bcrisPlusHom_algebraMap l x)

def bcrisInv : Formalism.Per6.Bcris l →+* Reformulated.AutPerF.Bcris l (OC l) :=
  Formalism.Per6.Loc2.lift
    ((algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))).comp (cA l).symm.toRingHom)
    (by
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_natCast,
        map_natCast]
      exact Reformulated.AutPerF.Bcris.isUnit_p (p := l) (R := OC l))
    (by
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, cA_symm_tA]
      exact Reformulated.AutPerF.Bcris.isUnit_logTeich (epsilon_isPrimitive l))

theorem bcrisInv_cB (x : ACris.ACris ℂ_[l] l) :
    bcrisInv l (Formalism.Per6.cB l x) = algebraMap _ (Reformulated.AutPerF.Bcris l (OC l)) ((cA l).symm x) :=
  Formalism.Per6.Loc2.lift_mk₀ _ _ _ x

theorem bcrisInv_bcrisHom (x : Reformulated.AutPerF.Bcris l (OC l)) : bcrisInv l (bcrisHom l x) = x := by
  have h : (bcrisInv l).comp (bcrisHom l) = RingHom.id _ := by
    refine Reformulated.AutPerF.Bcris.hom_ext fun y => ?_
    have h2 : ((bcrisInv l).comp (bcrisHom l)).comp
        (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) =
        (RingHom.id _).comp (algebraMap _ _) := by
      refine Reformulated.AutPerF.BcrisPlus.hom_ext fun z => ?_
      simp only [RingHom.comp_apply, RingHom.id_apply]
      change bcrisInv l (bcrisHom l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) _ z)) =
        algebraMap (Reformulated.AutPerF.Acris l (OC l)) _ z
      rw [bcrisHom_algebraMap, bcrisInv_cB, RingEquiv.symm_apply_apply]
    exact RingHom.congr_fun h2 y
  exact RingHom.congr_fun h x

theorem bcrisHom_bcrisInv (x : Formalism.Per6.Bcris l) : bcrisHom l (bcrisInv l x) = x := by
  have h : (bcrisHom l).comp (bcrisInv l) = RingHom.id _ := by
    refine Formalism.Per6.Loc2.hom_ext fun y => ?_
    change bcrisHom l (bcrisInv l (Formalism.Per6.cB l y)) = Formalism.Per6.cB l y
    rw [bcrisInv_cB, bcrisHom_algebraMap, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun h x

def cBc : Reformulated.AutPerF.Bcris l (OC l) ≃+* Formalism.Per6.Bcris l :=
  RingEquiv.ofRingHom (bcrisHom l) (bcrisInv l) (RingHom.ext (bcrisHom_bcrisInv l))
    (RingHom.ext (bcrisInv_bcrisHom l))

theorem cBc_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    cBc l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  bcrisHom_algebraMap l x

theorem cBc_symm_cB (x : ACris.ACris ℂ_[l] l) :
    (cBc l).symm (Formalism.Per6.cB l x) = algebraMap _ (Reformulated.AutPerF.Bcris l (OC l)) ((cA l).symm x) :=
  bcrisInv_cB l x

end Cmp6
