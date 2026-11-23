import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAlmostOntoOfLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNormGe

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem trace_almost_onto (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (_hL : ∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a :=
  AlmostTrace.trace_almost_onto_of_levels (GlobalTheory.Cyc.exists_trace_norm_ge l) K L S hKL hS hrep a ha ha1

end GlobalTheory.Cyc
