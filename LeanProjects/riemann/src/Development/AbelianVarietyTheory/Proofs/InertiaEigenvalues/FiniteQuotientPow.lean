import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem finite_quotient_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (n : ℕ) : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n}) := by
  have h : Ideal.span {((l : ℕ) : O) ^ n} =
      (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O) := by
    simp [Ideal.map_span]
  rw [h]
  haveI : Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}) := by
    rw [← PadicInt.ker_toZModPow]
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow (p := l) n))
  haveI : Module.Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})
      (O ⧸ (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  exact Module.finite_of_finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})

theorem isOpen_integers (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    IsOpen (Set.range (algebraMap ↥(OL LL) ↥LL.1)) := by
  have h : Set.range (algebraMap ↥(OL LL) ↥LL.1) =
      (fun x : ↥LL.1 => (x : PadicAlgCl l)) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    rw [Set.mem_preimage, mem_closedBall_zero_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val

theorem good_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) ∧ ∀ n : ℕ, Finite (↥(OL LL) ⧸ Ideal.span {((l : ℕ) : ↥(OL LL)) ^ n}) := by
  intro l _ LL
  haveI := LL.2
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := finite_integralClosure_padicInt l ↥LL.1
  haveI : ContinuousSMul ℚ_[l] ↥LL.1 :=
    Topology.IsInducing.continuousSMul (f := id) (g := fun x : ↥LL.1 => (x : PadicAlgCl l))
      Topology.IsInducing.subtypeVal continuous_id rfl
  haveI : IsTopologicalRing ↥LL.1 := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  refine ⟨⟨⟨inferInstance, isDiscreteValuationRing_integralClosure_padicInt l ↥LL.1,
    isFractionRing_integralClosure_padicInt l ↥LL.1⟩, LL.2, isModuleTopologyOfFiniteDimensional,
    inferInstance, isOpen_integers l LL⟩, finite_quotient_pow l _⟩

end GlobalTheory.LocalIntegers
