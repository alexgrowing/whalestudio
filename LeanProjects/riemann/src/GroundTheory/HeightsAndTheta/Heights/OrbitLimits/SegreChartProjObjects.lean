import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix

section Proj

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

open Classical in

def chartProjMatrix {m d : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) : Matrix (Fin d) (Fin m) ℂ :=
  fun r a => Ψ (fun i' => if σ a = i' then 1 else 0) r.succ

theorem chartProjMatrix_mulVec {m d : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) (x : Fin m → ℂ) (r : Fin d) :
    (chartProjMatrix σ Ψ *ᵥ x) r = Ψ (fun i' => x (σ.symm i')) r.succ := by
  classical
  have hv : (fun i' => x (σ.symm i')) = ∑ a, x a • fun i' => if σ a = i' then (1 : ℂ) else 0 := by
    rw [pi_eq_sum_univ (fun i' => x (σ.symm i'))]
    exact (Equiv.sum_comp σ _).symm.trans (by simp)
  rw [hv, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, chartProjMatrix]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

end Proj

section Chart

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def chartLiftDom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0}

theorem isOpen_chartLiftDom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    IsOpen (chartLiftDom σ i) :=
  ReciprocityTheory.ChartRestriction.G.Geo.isOpen_blockNonzero.preimage (contDiff_chartLift σ i (n := 0)).continuous

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_chartLiftDom_of_coord {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) : x ∈ chartLiftDom σ i :=
  chartLift_blockNonzero σ i hx

open Classical in

def chartWeight {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : (Fin m → ℂ) → ℝ :=
  (chartLiftDom σ i).piecewise (g ∘ chartLift σ i) 0

def chartPot {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (L : Fin e → HermLine ι) :
    Fin e → (Fin m → ℂ) → ℝ :=
  fun j => pot L j ∘ chartLift σ i

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartWeight_of_mem {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x ∈ chartLiftDom σ i) :
    chartWeight σ i g x = g (chartLift σ i x) := by
  classical
  simp only [chartWeight]
  rw [Set.piecewise_eq_of_mem _ _ _ hx]
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem chartWeight_of_coord {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) :
    chartWeight σ i g x = g (chartLift σ i x) :=
  chartWeight_of_mem g (mem_chartLiftDom_of_coord hx)

theorem measurable_chartWeight {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) : Measurable (chartWeight σ i g) := by
  classical
  have hc : ContinuousOn (g ∘ chartLift σ i) (chartLiftDom σ i) :=
    hg.1.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn fun _ hx => hx
  unfold chartWeight
  exact hc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) (isOpen_chartLiftDom σ i).measurableSet

theorem smoothNear_chartPot {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Set (Fin m → ℂ)}
    (hT : ∀ x ∈ T, x (σ.symm i) = 1) (j : Fin e) : SmoothNear T (chartPot σ i L j) := by
  refine ⟨chartLiftDom σ i, isOpen_chartLiftDom σ i, fun x hx => mem_chartLiftDom_of_coord (hT x hx), ?_⟩
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (L j).h (chartLift σ i x)) (chartLiftDom σ i) :=
    (hL j).comp (contDiff_chartLift σ i).contDiffOn fun _ hx => hx
  exact hh.log fun x hx => ((L j).pos _ hx).ne'

end Chart

end GroundTheory.Heights₂.Heights
