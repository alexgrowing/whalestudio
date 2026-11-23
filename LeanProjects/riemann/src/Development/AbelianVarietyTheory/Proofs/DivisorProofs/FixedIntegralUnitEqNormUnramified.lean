import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactOfComplete
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.UnitLemma

theorem UQ.norm_of_fixed_unit {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (w w' : E) (hs : star w = w) (h1 : ‖w‖ ≤ 1)
    (h1' : ‖w'‖ ≤ 1) (hww : w * w' = 1) : ∃ v : E, v * star v = w := by
  obtain ⟨ζ, -, hζ⟩ := GlobalTheory.NormUnits.exists_far_unit F E
  obtain ⟨a, ha⟩ := GlobalTheory.NormUnits.fixed_mem_range F E ζ hζ w hs
  have hprod : ‖w‖ * ‖w'‖ = 1 := by rw [← norm_mul, hww, norm_one]
  have hwn : ‖w‖ = 1 := by
    refine le_antisymm h1 ?_
    by_contra h
    push_neg at h
    have : ‖w‖ * ‖w'‖ < 1 :=
      calc ‖w‖ * ‖w'‖ ≤ ‖w‖ * 1 := by gcongr
        _ < 1 := by simpa using h
    linarith
  have han : ‖a‖ = 1 := by rw [← norm_algebraMap' E a, ha, hwn]
  obtain ⟨v, hv⟩ := GlobalTheory.NormUnits.norm_onto_units F E a han
  exact ⟨v, by rw [hv, ha]⟩

theorem UQ.unit_fixed_is_norm : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  intro K t ht hct
  obtain ⟨F, nF, nE, hE, nA, st, hU, hst, hball⟩ := K.exists_unram
  have hmul : ∀ x y : K.E, @HMul.hMul K.E K.E K.E (@instHMul K.E nE.toMul) x y = x * y := by
    intro x y; rw [← hE]
  have hone : @OfNat.ofNat K.E 1 (@One.toOfNat1 K.E nE.toOne) = 1 := by rw [← hE]
  obtain ⟨u, rfl⟩ := ht
  have hww : algebraMap K.O K.E u * algebraMap K.O K.E (u⁻¹ : K.Oˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨v, hv⟩ := @UQ.norm_of_fixed_unit F K.E nF nE nA st hU (algebraMap K.O K.E u)
    (algebraMap K.O K.E (u⁻¹ : K.Oˣ)) (by rw [hst]; exact hct) ((hball _).2 ⟨u, rfl⟩) ((hball _).2 ⟨_, rfl⟩)
    (by rw [hmul, hone]; exact hww)
  refine ⟨v, ?_⟩
  rw [← hst, ← hmul]; exact hv

end GlobalTheory.UnitLemma
