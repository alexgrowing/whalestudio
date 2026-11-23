import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRankTransfer
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotMassPos
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotDensVanish
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ProjRankTransfer.locallyConnectedSpace {e : ℕ} {X : Type*} [TopologicalSpace X]
    (A : FinHolAtlas e X) : LocallyConnectedSpace X := by
  let _ : ChartedSpace (Fin e → ℂ) X :=
    { atlas := Set.range A.chart
      chartAt := fun x => A.chart (chartIdx A x)
      mem_chart_source := fun x => Classical.choose_spec (A.cover x)
      chart_mem_atlas := fun x => ⟨_, rfl⟩ }
  exact ChartedSpace.locallyConnectedSpace (Fin e → ℂ) X

theorem ProjRankTransfer.of_found (hEq : ProjPotMassEq.Statement) (hPos : ProjPotMassPos.Statement)
    (hVan : ProjPotDensVanish.Statement) : ProjRankTransfer.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  by_contra hno
  push Not at hno
  have := ProjRankTransfer.locallyConnectedSpace BV
  have hCo : IsOpen (connectedComponent x) := isOpen_connectedComponent
  have h1 := hEq K ι P J n R Ψ V BV hH hC hΨ _ ⟨isClosed_connectedComponent, hCo⟩
  have h2 := hPos K ι P J n R V BV hH hC _ hCo ⟨x, mem_connectedComponent, hx⟩
  have h3 : mInt BV (fun _ => projPot R Ψ V)
      ((connectedComponent x).indicator fun _ => (1 : ℝ)) = 0 := by
    unfold mInt
    split_ifs with hP
    · unfold integralWith
      refine Finset.sum_eq_zero fun j _ => setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      by_cases hm : (BV.chart j).symm u ∈ connectedComponent x
      · rw [hVan K ι P J n R Ψ V BV hH hΨ j u hu (hno _ hm), mul_zero]
      · rw [Set.indicator_of_notMem hm, mul_zero, zero_mul]
    · rfl
  linarith

end GroundTheory.Heights₂.Heights.Targets
