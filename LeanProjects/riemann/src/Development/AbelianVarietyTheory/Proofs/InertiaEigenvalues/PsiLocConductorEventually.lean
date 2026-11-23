import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintaniStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasSatGLLocRep
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

open IsDedekindDomain Formalism.UG GlobalTheory.LFun

theorem GlobalTheory.JSW.psiLoc_conductor_eventually : ∀ (E : Type) [Field E] [NumberField E], ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w := by
  intro E _ _
  classical
  have hD : (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) ≠ 0 := differentIdeal_ne_bot (A := ℤ)
  obtain hfin := Ideal.finite_factors hD
  refine ⟨hfin.toFinset, fun w hw x => ?_⟩
  have hw' : ¬ w.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by simpa using hw
  rw [Ideal.dvd_iff_le] at hw'
  obtain ⟨y, hy, hyw⟩ := SetLike.not_le_iff_exists.mp hw'
  have hval : Valued.v ((algebraMap (𝓞 E) E y : E) : w.adicCompletion E) = 1 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (w.intValuation_le_one y) (not_lt.mp fun h => hyw ((w.intValuation_lt_one_iff_mem y).mp h))
  have key : x ∈ GroundTheory.Global.localInvDifferent w ↔ x ∈ w.adicCompletionIntegers E := by
    refine ⟨fun h => ?_, GroundTheory.Global.mem_localInvDifferent_of_mem⟩
    have h1 := h y hy
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, hval, mul_one] at h1
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1
  show _ ↔ x ∈ w.adicCompletionIntegers E
  rw [← key, ← GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff]
  refine forall₂_congr fun a _ => ?_
  rw [GlobalTheory.JSW.WhitModel.psiLoc_eq, Circle.coe_eq_one, mul_comm]
