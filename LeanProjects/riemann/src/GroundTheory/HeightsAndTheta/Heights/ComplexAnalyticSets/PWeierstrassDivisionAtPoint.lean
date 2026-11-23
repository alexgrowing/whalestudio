import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassDivision
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassDivisionAtPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

variable {τ : Type} [DecidableEq τ]

def lastToCoordinate (c : τ) : (Option {c' // c' ≠ c} → ℂ) →L[ℂ] (τ → ℂ) :=
  ContinuousLinearMap.pi fun c' =>
    if h : c' = c then ContinuousLinearMap.proj none else ContinuousLinearMap.proj (some ⟨c', h⟩)

def coordinateToLast (c : τ) : (τ → ℂ) →L[ℂ] (Option {c' // c' ≠ c} → ℂ) :=
  ContinuousLinearMap.pi fun o =>
    match o with
    | none => ContinuousLinearMap.proj c
    | some c' => ContinuousLinearMap.proj c'.1

theorem lastToCoordinate_apply (c : τ) (w : Option {c' // c' ≠ c} → ℂ) (c' : τ) :
    lastToCoordinate c w c' = if h : c' = c then w none else w (some ⟨c', h⟩) := by
  by_cases h : c' = c <;> simp [lastToCoordinate, h]

omit [DecidableEq τ] in
theorem coordinateToLast_none (c : τ) (y : τ → ℂ) : coordinateToLast c y none = y c := rfl

omit [DecidableEq τ] in
theorem coordinateToLast_some (c : τ) (y : τ → ℂ) (c' : {c' // c' ≠ c}) :
    coordinateToLast c y (some c') = y c'.1 := rfl

theorem lastToCoordinate_coordinateToLast (c : τ) (y : τ → ℂ) :
    lastToCoordinate c (coordinateToLast c y) = y := by
  funext c'
  rw [lastToCoordinate_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem lastToCoordinate_pointWithLast (c : τ) (s : ℂ) :
    lastToCoordinate c (pointWithLast 0 s) = Pi.single c s := by
  funext c'
  rw [lastToCoordinate_apply]
  split_ifs with h
  · subst h; simp [pointWithLast]
  · simp [pointWithLast, h]

theorem WeierstrassDivisionAtPoint.proof (hW : WeierstrassDivision.Statement) :
    WeierstrassDivisionAtPoint.Statement := by
  intro τ _ _ y₀ c d F g hF hg hord
  have hA : ∀ h : (τ → ℂ) → ℂ, AnalyticAt ℂ h y₀ →
      AnalyticAt ℂ (fun w => h (y₀ + lastToCoordinate c w)) 0 := by
    intro h hh
    exact AnalyticAt.fun_comp_of_eq hh (analyticAt_const.add ((lastToCoordinate c).analyticAt 0)) (by simp)
  have hord' : analyticOrderAt
      (fun t => (fun w => F (y₀ + lastToCoordinate c w)) (pointWithLast 0 t)) 0 = d := by
    simpa only [lastToCoordinate_pointWithLast] using hord
  obtain ⟨q, a, hq, ha, heq⟩ := hW {c' // c' ≠ c} d _ _ (hA F hF) (hA g hg) hord'
  refine ⟨fun y => q (coordinateToLast c (y - y₀)), fun j u => a j (fun c' => u c'.1 - y₀ c'.1), ?_, ?_, ?_⟩
  · exact AnalyticAt.fun_comp_of_eq hq
      (((coordinateToLast c).analyticAt _).comp (analyticAt_id.sub analyticAt_const)) (by simp)
  · intro j
    have hR : AnalyticAt ℂ (fun u : τ → ℂ => fun c' : {c' // c' ≠ c} => u c'.1 - y₀ c'.1) (zeroCoordinate c y₀) := by
      have hL := ((ContinuousLinearMap.pi fun c' : {c' // c' ≠ c} =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c'.1).analyticAt (zeroCoordinate c y₀)).sub
          (analyticAt_const (v := fun c' : {c' // c' ≠ c} => y₀ c'.1))
      convert hL using 1
      funext u c'
      rfl
    refine AnalyticAt.fun_comp_of_eq (ha j) hR ?_
    funext c'
    simp [zeroCoordinate_apply, c'.2]
  · have hT : Tendsto (fun y => coordinateToLast c (y - y₀)) (𝓝 y₀) (𝓝 0) := by
      have hc : Continuous fun y : τ → ℂ => coordinateToLast c (y - y₀) :=
        (coordinateToLast c).continuous.comp (continuous_id.sub continuous_const)
      simpa using hc.tendsto y₀
    filter_upwards [hT.eventually heq] with y hy
    have hy' : y₀ + lastToCoordinate c (coordinateToLast c (y - y₀)) = y := by
      rw [lastToCoordinate_coordinateToLast]; abel
    simp only [hy'] at hy
    rw [hy]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun i : {c' // c' ≠ c} => coordinateToLast c (y - y₀) (some i)) =
        fun c' => zeroCoordinate c y c'.1 - y₀ c'.1 := by
      funext c'
      rw [coordinateToLast_some, zeroCoordinate_apply, if_neg c'.2, Pi.sub_apply]
    rw [h1, coordinateToLast_none, Pi.sub_apply]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
