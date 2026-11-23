import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropFTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HBBound
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PrimeLogSum

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Flat.Bound₂

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_C_mul (a : ℝ) (Q : RP Ψ N) : degFl (C a * Q) = a * degFl Q := by
  unfold degFl
  simp only [coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

def rk (N j : ℕ) : Ψ ⊕ Ψ → ℝ
  | Sum.inl _ => j
  | Sum.inr _ => (N : ℝ) - j

def ep (N j p : ℕ) (fr : ℕ → Ψ ⊕ Ψ) : ℝ := (∑' n : ℕ, ((p : ℝ)⁻¹) ^ (n + 1) * rk N j (fr n)) - j / ((p : ℝ) - 1)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem pLie_zero {j : ℕ} (hj : j ≤ N) (s : Ψ ⊕ Ψ) : (pLie j 0 s : RP Ψ N) = C (rk N j s) := by
  have hc : (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
    rw [Fin.card_filter_val_lt]; omega
  have hc' : (Finset.univ.filter fun i : Fin N => j ≤ (i : ℕ)).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  cases s with
  | inl τ => simp [pLie, pkLow, rk, hc]
  | inr τ => simp [pLie, rk, hc', Nat.cast_sub hj]

theorem delta_one {j : ℕ} (hj : j ≤ N) (p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ) (Q : RP Ψ N) :
    deltaTerm j p τ fr 1 Q = ep N j p fr * Real.log p * degFl Q := by
  have h2 : (pkLow j τ 0 : RP Ψ N) = C (j : ℝ) := pLie_zero hj (Sum.inl τ)
  unfold deltaTerm ep
  simp only [Nat.sub_self, pLie_zero hj, h2, degFl_C_mul, pow_one, ← mul_assoc]
  rw [tsum_mul_right]
  push_cast
  ring

variable (T : RootTower Ψ N) (II : IntersectionSystem)

omit [Fintype Ψ] [DecidableEq Ψ] in

theorem abs_ep_le {j p : ℕ} (hj : j ≤ N) (hp : 2 ≤ p) (fr : ℕ → Ψ ⊕ Ψ) : |ep N j p fr| ≤ N / ((p : ℝ) - 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg : HasSum (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * N) (N / ((p : ℝ) - 1)) := by
    have := ((hasSum_geometric_of_lt_one hr0 hr1).mul_right (p : ℝ)⁻¹).mul_right (N : ℝ)
    have e : (1 - (p : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ * N = N / ((p : ℝ) - 1) := by
      have : (p : ℝ) ≠ 0 := by linarith
      have := h1.ne'
      field_simp
    rw [e] at this
    simpa only [pow_succ] using this
  have hrk : ∀ s : Ψ ⊕ Ψ, 0 ≤ rk N j s ∧ rk N j s ≤ N := by
    rintro (s | s) <;> simp only [rk] <;> constructor <;> linarith
  have hle : ∀ n : ℕ, ((p : ℝ)⁻¹) ^ (n + 1) * rk N j (fr n) ≤ ((p : ℝ)⁻¹) ^ (n + 1) * N := fun n =>
    mul_le_mul_of_nonneg_left (hrk _).2 (by positivity)
  have hnn : ∀ n : ℕ, 0 ≤ ((p : ℝ)⁻¹) ^ (n + 1) * rk N j (fr n) := fun n => mul_nonneg (by positivity) (hrk _).1
  have hs := Summable.of_nonneg_of_le hnn hle hg.summable
  have hU := hs.tsum_le_tsum hle hg.summable
  rw [hg.tsum_eq] at hU
  have hL : 0 ≤ ∑' n : ℕ, ((p : ℝ)⁻¹) ^ (n + 1) * rk N j (fr n) := tsum_nonneg hnn
  have a1 : (j : ℝ) / ((p : ℝ) - 1) ≤ N / ((p : ℝ) - 1) := by gcongr
  have a2 : 0 ≤ (j : ℝ) / ((p : ℝ) - 1) := by positivity
  unfold ep
  exact abs_le.2 ⟨by linarith, by linarith⟩

end GlobalTheory.CompanionTheory.Ar.Flat.Bound₂
