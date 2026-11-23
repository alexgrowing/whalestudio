import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

namespace GlobalTheory.CompanionTheory.Ar.JetLeib

theorem jet_mul_first {u v : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0) (i : ℕ)
    (h0 : ∀ k < i, iteratedDeriv k u 0 = 0) :
    (∀ k < i, iteratedDeriv k (fun t => u t * v t) 0 = 0) ∧
      iteratedDeriv i (fun t => u t * v t) 0 = v 0 * iteratedDeriv i u 0 := by
  have key : ∀ n : ℕ, iteratedDeriv n (fun t => u t * v t) 0 =
      ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℂ) * iteratedDeriv m u 0 * iteratedDeriv (n - m) v 0 := fun n =>
    iteratedDeriv_fun_mul hu.contDiffAt hv.contDiffAt
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [key k]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmk : m < i := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hk
    rw [h0 m hmk]
    simp
  · rw [key i, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    · simp [mul_comm]
    · intro m hm
      rw [h0 m (Finset.mem_range.mp hm)]
      simp

theorem jet_first_nonzero : ∀ (r : ℕ) (Ψ : Fin r → ℂ → ℂ) (c : Fin r → ℂ) (h F : ℂ → ℂ), (∀ j, AnalyticAt ℂ (Ψ j) 0) → AnalyticAt ℂ F 0 → F 0 ≠ 0 → (∀ᶠ τ in 𝓝 (0 : ℂ), ∑ j, c j * Ψ j τ = h τ * F τ) → ∀ i : ℕ, ((∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) ↔ ∀ k < i, iteratedDeriv k h 0 = 0) ∧ ((∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) → ∑ j, c j * iteratedDeriv i (Ψ j) 0 = F 0 * iteratedDeriv i h 0) := by
  intro r Ψ c h F hΨ hF hF0 hev i
  have hP : AnalyticAt ℂ (fun τ => ∑ j, c j * Ψ j τ) 0 :=
    Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul (hΨ j)
  have hDP : ∀ k : ℕ, iteratedDeriv k (fun τ => ∑ j, c j * Ψ j τ) 0 =
      ∑ j, c j * iteratedDeriv k (Ψ j) 0 := by
    intro k
    have hc : ∀ j ∈ (Finset.univ : Finset (Fin r)),
        ContDiffAt ℂ k (fun τ => c j * Ψ j τ) 0 := fun j _ =>
      (analyticAt_const.mul (hΨ j)).contDiffAt
    rw [iteratedDeriv_fun_sum (f := fun j τ => c j * Ψ j τ) hc]
    exact Finset.sum_congr rfl fun j _ => iteratedDeriv_const_mul_field (c j) (Ψ j)
  have hFi : AnalyticAt ℂ (fun t => (F t)⁻¹) 0 := hF.inv hF0
  have hne : ∀ᶠ τ in 𝓝 (0 : ℂ), F τ ≠ 0 := hF.continuousAt.eventually_ne hF0
  have hh : h =ᶠ[𝓝 (0 : ℂ)] fun t => (∑ j, c j * Ψ j t) * (F t)⁻¹ := by
    filter_upwards [hev, hne] with τ h1 h2
    rw [h1, _root_.mul_assoc, mul_inv_cancel₀ h2, _root_.mul_one]
  have hha : AnalyticAt ℂ h 0 := (hP.mul hFi).congr hh.symm
  have hPe : (fun τ => ∑ j, c j * Ψ j τ) =ᶠ[𝓝 (0 : ℂ)] fun t => h t * F t := hev
  have hDPh : ∀ k : ℕ, ∑ j, c j * iteratedDeriv k (Ψ j) 0 =
      iteratedDeriv k (fun t => h t * F t) 0 := fun k => by
    rw [← hDP k]; exact hPe.iteratedDeriv_eq k
  have hDh : ∀ k : ℕ, iteratedDeriv k h 0 =
      iteratedDeriv k (fun t => (∑ j, c j * Ψ j t) * (F t)⁻¹) 0 := fun k =>
    hh.iteratedDeriv_eq k
  have back : (∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) →
      ∀ k < i, iteratedDeriv k h 0 = 0 := by
    intro hz k hk
    rw [hDh k]
    exact (jet_mul_first hP hFi i fun k hk => by rw [hDP k]; exact hz k hk).1 k hk
  refine ⟨⟨back, fun hz k hk => ?_⟩, fun hz => ?_⟩
  · rw [hDPh k]
    exact (jet_mul_first hha hF i hz).1 k hk
  · rw [hDPh i]
    exact (jet_mul_first hha hF i (back hz)).2

end GlobalTheory.CompanionTheory.Ar.JetLeib
