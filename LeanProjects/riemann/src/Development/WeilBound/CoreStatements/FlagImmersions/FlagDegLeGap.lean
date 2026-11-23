import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormulaStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem prod_le_mul_two_pow_card {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) (x₀ : ι) (c : ℝ) (hc : f x₀ = c) :
    ∏ x, f x ≤ c * 2 ^ Fintype.card ι := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ x₀), hc]
  refine mul_le_mul_of_nonneg_left ?_ (hc ▸ h0 x₀)
  calc ∏ x ∈ Finset.univ.erase x₀, f x ≤ ∏ x ∈ Finset.univ.erase x₀, (2 : ℝ) :=
        Finset.prod_le_prod (fun x _ => h0 x) (fun x _ => h2 x)
    _ = 2 ^ (Finset.univ.erase x₀).card := Finset.prod_const 2
    _ ≤ 2 ^ Fintype.card ι := pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

theorem flagDeg_le_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  intro Ψ _ _ N j hj hjN
  refine ⟨((GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N).factorial : ℝ) * 2 ^ Fintype.card (Ψ × Fin N × Fin N),
    by positivity, ?_⟩
  intro lam τ₀ hlam hdom
  have hj1 : j - 1 < N := by omega
  have hbound : ∀ τ i, |lam τ i| ≤ 1 := by
    intro τ i
    have h1 := norm_le_pi_norm (show Ψ → Fin N → ℝ from lam) τ
    have h2 := norm_le_pi_norm (lam τ) i
    rw [Real.norm_eq_abs] at h2
    have h3 : ‖(show Ψ → Fin N → ℝ from lam)‖ ≤ 1 := hlam
    linarith
  have hfac : ∀ τ (i k : Fin N),
      0 ≤ (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) ∧
        (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) ≤ 2 := by
    intro τ i k
    split_ifs with hik
    · have hik' : (i : ℕ) < (k : ℕ) := hik
      have hd : ((i : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hik'
      have hmono := hdom τ i k hik.le
      have hi := abs_le.mp (hbound τ i)
      have hk := abs_le.mp (hbound τ k)
      constructor
      · apply div_nonneg <;> linarith
      · rw [div_le_iff₀ (by linarith)]
        linarith
    · norm_num
  have hgap : GlobalTheory.CompanionTheory.Ar.Top.gap j lam τ₀ = lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩ := by
    unfold GlobalTheory.CompanionTheory.Ar.Top.gap GlobalTheory.CompanionTheory.Ar.Top.ent
    rw [dif_pos hj1, dif_pos hjN]
  have hx0 : (if (⟨j - 1, hj1⟩ : Fin N) < ⟨j, hjN⟩ then
      (lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩) /
        ((((⟨j, hjN⟩ : Fin N) : ℕ) : ℝ) - (((⟨j - 1, hj1⟩ : Fin N) : ℕ) : ℝ)) else 1) =
      lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩ := by
    have hlt : (⟨j - 1, hj1⟩ : Fin N) < ⟨j, hjN⟩ := by
      rw [Fin.lt_def]
      show j - 1 < j
      omega
    rw [if_pos hlt]
    have hden : (((⟨j, hjN⟩ : Fin N) : ℕ) : ℝ) - (((⟨j - 1, hj1⟩ : Fin N) : ℕ) : ℝ) = 1 := by
      show ((j : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ) = 1
      rw [Nat.cast_sub hj, Nat.cast_one]
      ring
    rw [hden, div_one]
  have key := prod_le_mul_two_pow_card
    (fun x : Ψ × Fin N × Fin N => if x.2.1 < x.2.2 then
      (lam x.1 x.2.1 - lam x.1 x.2.2) / (((x.2.2 : ℕ) : ℝ) - ((x.2.1 : ℕ) : ℝ)) else 1)
    (fun x => (hfac x.1 x.2.1 x.2.2).1) (fun x => (hfac x.1 x.2.1 x.2.2).2)
    (τ₀, ⟨j - 1, hj1⟩, ⟨j, hjN⟩) _ hx0
  simp only [Fintype.prod_prod_type] at key
  obtain ⟨hdeg, -, -⟩ := GlobalTheory.T.flag_degree_weight_formula Ψ N lam
  rw [hdeg, hgap]
  calc _ ≤ ((GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N).factorial : ℝ) *
        ((lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩) * 2 ^ Fintype.card (Ψ × Fin N × Fin N)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

end RootFieldNumerics
