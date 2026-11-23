import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem isTest_indicator_one_of_clopen_compact {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    (hK : IsCompact S) : IsTest (Set.indicator S (1 : X → ℂ)) := by
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hS.isOpen.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hK hS.isClosed fun x hx => Set.indicator_of_notMem hx _

theorem isTest_unitU (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E]
    [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ)
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) : IsTest (unitU r F E) := by
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace E
  haveI : ContinuousStar E := ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) hstar).continuous⟩
  have hF : {x : F | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by ext x; simp
  have hE : {x : E | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by ext x; simp
  have cF : IsClopen {x : F | ‖x‖ ≤ 1} := hF ▸ IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have cE : IsClopen {x : E | ‖x‖ ≤ 1} := hE ▸ IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have kF : IsCompact {x : F | ‖x‖ ≤ 1} := hF ▸ isCompact_closedBall _ _
  have kE : IsCompact {x : E | ‖x‖ ≤ 1} := hE ▸ isCompact_closedBall _ _
  have cV : IsClopen {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1} := by
    rw [Set.ofPred_forall]
    exact isClopen_iInter_of_finite fun i => cE.preimage (continuous_apply i)
  have kV : IsCompact {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1} := isCompact_pi_infinite fun _ => kE
  have cM : IsClopen {A : Matrix (Fin r) (Fin r) E | ∀ i j, ‖A i j‖ ≤ 1} := by
    rw [Set.ofPred_forall]
    exact isClopen_iInter_of_finite fun i => cV.preimage (continuous_apply i)
  have kM : IsCompact {A : Matrix (Fin r) (Fin r) E | ∀ i j, ‖A i j‖ ≤ 1} :=
    isCompact_pi_infinite (s := fun _ : Fin r => {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1}) fun _ => kV
  have hcl : IsClosed ((selfAdjoint (Matrix (Fin r) (Fin r) E)) : Set (Matrix (Fin r) (Fin r) E)) :=
    isClosed_eq continuous_star continuous_id
  have cA : IsClopen {A : selfAdjoint (Matrix (Fin r) (Fin r) E) | ∀ i j, ‖A.1 i j‖ ≤ 1} :=
    cM.preimage continuous_subtype_val
  have kA : IsCompact {A : selfAdjoint (Matrix (Fin r) (Fin r) E) | ∀ i j, ‖A.1 i j‖ ≤ 1} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage kM
  exact isTest_indicator_one_of_clopen_compact (cA.prod (cV.prod cF)) (kA.prod (kV.prod kF))

end GlobalTheory.JR
