import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IdemPairCpt

open GlobalTheory.StdFrames

theorem cpt_sg_eq_one_of_cP_mem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∈ P) : cpt (D := D) w (sg D (toEAf D e)) = 1 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (1 - toEAf D e) = 0 := by
    rw [map_sub, map_one, GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, sub_self]
  have h2 := cpt_sg_eq_zero h1
  rw [map_sub, map_one, map_sub, map_one] at h2
  exact (sub_eq_zero.mp h2).symm

theorem cpt_sg_eq_zero_of_cP_notMem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∉ P) : cpt (D := D) w (sg D (toEAf D e)) = 0 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (toEAf D e) = 0 := by
    rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw]
  exact cpt_sg_eq_zero h1

theorem cpt_add_cA_idemSum : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := by
  intro D e P he w
  have hsplit : GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) =
      cpt (D := D) w (toEAf D e) + cpt (D := D) w (sg D (toEAf D e)) := by
    rw [map_add, toEAf_cA, map_add]
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · rw [hsplit]
    by_cases hw : w ∈ P
    · have hc : GlobalTheory.IdemSupport.cP w ∉ P := fun hc => GlobalTheory.IdemSumBranch.conjPrime_ne he hc hw rfl
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, cpt_sg_eq_zero_of_cP_notMem he w hc, add_zero]
    · have hc : GlobalTheory.IdemSupport.cP w ∈ P := h.resolve_left hw
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw, cpt_sg_eq_one_of_cP_mem he w hc, zero_add]
  · rw [hsplit, GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg h1, cpt_sg_eq_zero_of_cP_notMem he w h2, add_zero]

example : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := @cpt_add_cA_idemSum

end GlobalTheory.IdemPairCpt
