import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)

section Chart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def segreChartSet (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def segreChartIdeal (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (segreChartSet P σ i)

def segreChartComponents (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (segreChartIdeal P σ i)).toFinset

omit [∀ k, Fintype (ι k)] in
theorem mem_segreChartComponents {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ segreChartComponents P σ i ↔ J ∈ (segreChartIdeal P σ i).minimalPrimes :=
  Set.Finite.mem_toFinset _

omit [∀ k, Fintype (ι k)] in

theorem chart_coord_eq_one {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {x : Fin m → ℂ} (hx : x ∈ ComplexSets.zeroSet J) : x (σ.symm i) = 1 := by
  have hle : segreChartIdeal P σ i ≤ J := (mem_segreChartComponents.1 hJ).1.2
  have hmem : (MvPolynomial.X (σ.symm i) - 1 : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i := by
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    simp [hzi]
  have h := hx _ (hle hmem)
  simp only [map_sub, MvPolynomial.eval_X, map_one] at h
  exact sub_eq_zero.1 h

end Chart

section Lift

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ) :
    (Σ k, ι k) → ℂ :=
  fun p => x (σ.symm (Function.update i p.1 p.2))

theorem contDiff_chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) {n : WithTop ℕ∞} :
    ContDiff ℝ n (chartLift σ i) :=
  contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (σ.symm (Function.update i p.1 p.2))

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem chartLift_blockNonzero {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) : ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0 :=
  fun k => ⟨i k, by simp [chartLift, hx]⟩

omit [∀ k, Fintype (ι k)] in

theorem chartLift_segre_apply {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) (k : K) (j : ι k) :
    chartLift σ i (fun a => segre z (σ a)) ⟨k, j⟩ = z ⟨k, j⟩ * (z ⟨k, i k⟩)⁻¹ := by
  have hne : z ⟨k, i k⟩ ≠ 0 := fun h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hz] at this
    exact one_ne_zero this
  have hupd : (fun k' => z ⟨k', Function.update i k j k'⟩) =
      Function.update (fun k' => z ⟨k', i k'⟩) k (z ⟨k, j⟩) := by
    funext k'
    by_cases h : k' = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hprod : segre z (Function.update i k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ := by
    simp only [segre]
    rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hall : z ⟨k, i k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ = 1 := by
    rw [Finset.mul_prod_erase _ (fun k' => z ⟨k', i k'⟩) (Finset.mem_univ k)]
    exact hz
  simp only [chartLift, Equiv.apply_symm_apply]
  rw [hprod]
  field_simp
  linear_combination z ⟨k, j⟩ * hall

theorem segre_chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) :
    segre (chartLift σ i (fun a => segre z (σ a))) = segre z := by
  funext i'
  show ∏ k, chartLift σ i (fun a => segre z (σ a)) ⟨k, i' k⟩ = ∏ k, z ⟨k, i' k⟩
  simp only [chartLift_segre_apply σ i z hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have : ∏ k, z ⟨k, i k⟩ = 1 := hz
  rw [this, inv_one, mul_one]

end Lift

end GroundTheory.Heights₂.Heights
