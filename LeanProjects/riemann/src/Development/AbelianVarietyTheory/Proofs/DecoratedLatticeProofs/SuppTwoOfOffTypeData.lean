import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAllStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumRestrictionRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateCompactMemLevel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

namespace GlobalTheory.FinPl.SuppTwoAsm

set_option maxHeartbeats 800000 in
theorem ginf_le_grpOff {D : D7} (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, congGrp, MonoidHom.mem_ker]
  have h1 := Units.ext_iff.mp ha
  simp only [finHom, Formalism.UG.bc, MonoidHom.comp_apply, Units.coe_map, Units.val_one] at h1
  apply Units.ext
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  simp only [MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe] at h2
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe]
  have hf : (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = finPart D := rfl
  rw [hf] at h2
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h2 ⊢
    rw [← map_one (Ideal.Quotient.mk (idOff D P)), Ideal.Quotient.eq, idOff, Ideal.mem_iInf]
    intro w
    have h3 : compAt D w.1 ((matHom V a).val i i) = compAt D w.1 1 := by
      rw [compAt, RingHom.comp_apply, RingHom.comp_apply, h2, RingHom.map_one]
      exact (RingHom.map_one _).symm
    rw [RingHom.mem_ker, RingHom.map_sub, h3, sub_self]
  · rw [Matrix.one_apply_ne hij] at h2 ⊢
    rw [Ideal.Quotient.eq_zero_iff_mem, idOff, Ideal.mem_iInf]
    intro w
    rw [RingHom.mem_ker, compAt, RingHom.comp_apply, h2, map_zero]

end GlobalTheory.FinPl.SuppTwoAsm
