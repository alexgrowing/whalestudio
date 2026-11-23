import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInfty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRootStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolynomialRelationPassesToQExpansionsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem qAll_isBoundedAtImInfty {p : ℂ → Prop} {N : ℕ} {f : ℍ → ℂ} (hN : 0 < N) (h : QAll p N f) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  obtain ⟨a, ha, -⟩ := h
  exact (GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN ha).2

theorem isBoundedAtImInfty_of_monic_root {n : ℕ} {h : ℍ → ℂ} {s : Fin n → ℍ → ℂ}
    (hs : ∀ j, UpperHalfPlane.IsBoundedAtImInfty (s j))
    (hrel : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) : UpperHalfPlane.IsBoundedAtImInfty h := by
  have hb : ∀ τ, ‖h τ‖ ≤ 1 + ∑ j, ‖s j τ‖ := fun τ => GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff n (fun j => s j τ) (h τ) (hrel τ)
  have hsum : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
    refine Asymptotics.IsBigO.add (Asymptotics.isBigO_refl _ _) ?_
    convert Asymptotics.IsBigO.sum (A := fun j τ => ‖s j τ‖) (s := Finset.univ) (fun j _ => (hs j).norm_left) using 1
    ext τ; simp [Finset.sum_apply]
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_of_le _ fun τ => ?_) hsum
  refine (hb τ).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

end GlobalTheory.FN

namespace GlobalTheory.FN

theorem qAll_range_of_monic_root : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (N n : ℕ) (h : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ) → (∀ j, QAll (· ∈ ε.range) N (s j)) → (∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) → QAll (· ∈ ε.range) N h := by
  intro Ω _ _ ε N n h s hN hh hper hs hrel
  obtain ⟨b, hb⟩ := GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic N h hN hh hper
    (isBoundedAtImInfty_of_monic_root (fun j => qAll_isBoundedAtImInfty hN (hs j)) hrel)
  choose a ha hain using hs
  let p : ℕ → ℍ → ℂ := fun i => if hi : i < n then s ⟨i, hi⟩ else fun _ => 1
  let c : ℕ → ℕ → ℂ := fun i => if hi : i < n then a ⟨i, hi⟩ else fun k => if k = 0 then 1 else 0
  have hp : ∀ i, HasQ N (p i) (c i) := by
    intro i
    by_cases hi : i < n
    · simpa [p, c, hi] using ha ⟨i, hi⟩
    · simpa [p, c, hi] using HasQ.const N 1
  have hrel' : ∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * h τ ^ i = 0 := by
    intro τ
    rw [Finset.sum_range_succ, Finset.sum_range, add_comm, ← hrel τ]
    simp [p]
  have hQ := GlobalTheory.T.polynomial_relation_passes_to_qExpansions N n h b p c hN hb hp hrel'
  set Q := ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i)) with hQdef
  have hcoeff : ∀ i, Q.coeff i = if i < n + 1 then PowerSeries.mk (c i) else 0 := by
    intro i
    rw [hQdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i (fun j => PowerSeries.mk (c j))]
    simp
  have hcn : PowerSeries.mk (c n) = 1 := by
    ext k
    simp [c, PowerSeries.coeff_one]
  have hQ0 : Q ≠ 0 := by
    intro h0
    have := hcoeff n
    rw [h0, if_pos (Nat.lt_succ_self n), hcn] at this
    simp at this
  have hcr : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range := by
    intro i k
    rw [hcoeff i]
    split_ifs with hi
    · rw [PowerSeries.coeff_mk]
      by_cases hin : i < n
      · simpa [c, hin] using hain ⟨i, hin⟩ k
      · simp only [c, hin, dite_false]
        split_ifs
        · exact ⟨1, map_one ε⟩
        · exact ⟨0, map_zero ε⟩
    · simp only [map_zero]
      exact ⟨0, map_zero ε⟩
  have key := GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range Ω ε (PowerSeries.mk b) Q hQ0 hcr hQ
  exact ⟨b, hb, fun k => by simpa using key k⟩

end GlobalTheory.FN
