import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.InverseCompactOpen

theorem inv_exists_compact_open (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F)
    (hU : IsOpen U) (ha : a₀ ∈ U) :
    ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := by
  have hUn : Unram F E := inferInstance
  haveI : LocallyCompactSpace F := hUn.lcF
  haveI : IsUltrametricDist F := hUn.ultraF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU a₀ ha
  have hε2 : 0 < ε / 2 := half_pos hε
  refine ⟨Metric.closedBall a₀ (ε / 2), isCompact_closedBall _ _, ?_,
    Metric.mem_closedBall_self hε2.le, ?_⟩
  · have hpi : ∀ x : Fin r → F, IsOpen (Metric.closedBall x (ε / 2)) := by
      intro x
      rw [closedBall_pi x hε2.le]
      exact isOpen_set_pi Set.finite_univ
        (fun i _ => IsUltrametricDist.isOpen_closedBall (x i) hε2.ne')
    obtain ⟨p, q, l⟩ := a₀
    rw [← closedBall_prod_same, ← closedBall_prod_same]
    exact (hpi p).prod ((hpi q).prod (IsUltrametricDist.isOpen_closedBall l hε2.ne'))
  · exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball

end GlobalTheory.InverseCompactOpen
