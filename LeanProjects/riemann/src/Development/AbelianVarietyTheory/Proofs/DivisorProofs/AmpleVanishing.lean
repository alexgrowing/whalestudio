import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAcyclicOfCechVanishingAllCoversStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingLineBundleInvMixOneZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyCechVanishingAboveDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreVanishingLineBundleInvMixFixedDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogenyStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.AmpleGen

namespace GlobalTheory.AmpleGen

theorem stepTwo {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (h2 : (2 : K) ≠ 0) (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (h : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (2 * a : ℕ) (2 * b : ℕ)) j₁ ∧
      NV A (mix A L (a + b : ℕ) (a + b : ℕ)) j₂ := by
  have hd : (((1 : ℤ) * (-1) - 1 * 1 : ℤ) : K) ≠ 0 := by
    have : (((1 : ℤ) * (-1) - 1 * 1 : ℤ) : K) = -2 := by push_cast; ring
    rw [this]; exact neg_ne_zero.2 h2
  obtain ⟨j₁, j₂, e, h₁, h₂⟩ := GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny K A hA 1 1 1 (-1) (by norm_num) hd L hL a b j h
  have t1 : tri 1 = 1 := by decide
  have t0 : tri (-1) = 0 := by decide
  simp only [t1, t0, neg_neg] at h₁ h₂
  refine ⟨j₁, j₂, e, ?_, ?_⟩
  · convert h₁ using 2 <;> push_cast <;> ring
  · convert h₂ using 2 <;> push_cast <;> ring

theorem stepFive {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (h5 : (5 : K) ≠ 0) (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (h : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (4 * a + b : ℕ) (a + 4 * b : ℕ)) j₁ ∧
      NV A (mix A L (3 * a + 2 * b : ℕ) (2 * a + 3 * b : ℕ)) j₂ := by
  have hd : (((1 : ℤ) * (-1) - 2 * 2 : ℤ) : K) ≠ 0 := by
    have : (((1 : ℤ) * (-1) - 2 * 2 : ℤ) : K) = -5 := by push_cast; ring
    rw [this]; exact neg_ne_zero.2 h5
  obtain ⟨j₁, j₂, e, h₁, h₂⟩ := GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny K A hA 1 2 2 (-1) (by norm_num) hd L hL a b j h
  have t1 : tri 1 = 1 := by decide
  have t0 : tri (-1) = 0 := by decide
  have t2 : tri 2 = 3 := by decide
  have t2' : tri (-2) = 1 := by decide
  simp only [t1, t0, t2, t2', neg_neg] at h₁ h₂
  refine ⟨j₁, j₂, e, ?_, ?_⟩
  · convert h₁ using 2 <;> push_cast <;> ring
  · convert h₂ using 2 <;> push_cast <;> ring

theorem step {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (L : LB A.left) (hL : L.IsLB) (a b i : ℕ) (h : NV A (mix A L a b) i) :
    ∃ (i₁ i₂ a₁ b₁ a₂ b₂ : ℕ), i₁ + i₂ = 2 * i ∧ NV A (mix A L a₁ b₁) i₁ ∧ NV A (mix A L a₂ b₂) i₂ ∧
      a + b ≤ a₁ + b₁ ∧ 2 * (a + b) ≤ a₂ + b₂ ∧ ((a₂ : ℤ) - b₂ = (a : ℤ) - b ∨ (a₂ : ℤ) - b₂ = 0) := by
  by_cases h2 : (2 : K) = 0
  · have h5 : (5 : K) ≠ 0 := by
      have : (5 : K) = 2 * 2 + 1 := by norm_num
      rw [this, h2]; simp
    obtain ⟨i₁, i₂, e, h₁, h₂⟩ := stepFive A hA h5 L hL a b i h
    refine ⟨i₁, i₂, _, _, _, _, e, h₁, h₂, by omega, by omega, Or.inl (by push_cast; ring)⟩
  · obtain ⟨i₁, i₂, e, h₁, h₂⟩ := stepTwo A hA h2 L hL a b i h
    refine ⟨i₁, i₂, _, _, _, _, e, h₁, h₂, by omega, by omega, Or.inr (by push_cast; ring)⟩

theorem ampleVanishing : GlobalTheory.Published.AmpleVanishing := by
  intro K _ _ A _ hA L hL hamp
  refine GlobalTheory.T.relativelyAcyclic_of_cech_vanishing_all_covers K A L fun j hj => ?_
  have h0 := GlobalTheory.T.cechNonvanishing_lineBundleInvMix_one_zero K A L hL _ hj
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianVariety_cech_vanishing_above_degree K A hA
  have hLB : ∀ a b : ℤ, (mix A L a b).IsLB := fun a b => LB.isLB_linComb hL _ _

  let S : ℕ → Prop := fun i => 1 ≤ i ∧ ∃ a b : ℕ, 1 ≤ a + b ∧ NV A (mix A L a b) i
  have hS : ∀ i, S i → i ≤ c := fun i ⟨_, a, b, _, h⟩ =>
    le_of_lt (not_le.1 fun hi => hc _ (hLB a b) i hi h)
  have hj1 : S (j + 1) := ⟨by omega, 1, 0, by omega, by exact_mod_cast h0⟩
  classical
  let T := Nat.findGreatest S c
  have hT : S T := Nat.findGreatest_spec (hS _ hj1) hj1
  have hmax : ∀ i, S i → i ≤ T := fun i hi => Nat.le_findGreatest (hS i hi) hi
  obtain ⟨hT1, a, b, hab, hTab⟩ := hT

  have next : ∀ a' b' : ℕ, 1 ≤ a' + b' → NV A (mix A L a' b') T → ∃ a₂ b₂ : ℕ,
      NV A (mix A L a₂ b₂) T ∧ 2 * (a' + b') ≤ a₂ + b₂ ∧
        ((a₂ : ℤ) - b₂ = (a' : ℤ) - b' ∨ (a₂ : ℤ) - b₂ = 0) := by
    intro a' b' h1 h
    obtain ⟨i₁, i₂, a₁, b₁, a₂, b₂, e, h₁, h₂, l₁, l₂, hd⟩ := step A hA L hL a' b' T h
    have u₁ : i₁ ≤ T := by
      rcases Nat.eq_zero_or_pos i₁ with h0 | h0
      · omega
      · exact hmax _ ⟨h0, a₁, b₁, by omega, h₁⟩
    have u₂ : i₂ ≤ T := by
      rcases Nat.eq_zero_or_pos i₂ with h0 | h0
      · omega
      · exact hmax _ ⟨h0, a₂, b₂, by omega, h₂⟩
    exact ⟨a₂, b₂, by rwa [show i₂ = T by omega] at h₂, l₂, hd⟩
  have grow : ∀ n : ℕ, ∃ a' b' : ℕ, 1 ≤ a' + b' ∧ n ≤ a' + b' ∧ NV A (mix A L a' b') T ∧
      ((a' : ℤ) - b' = (a : ℤ) - b ∨ (a' : ℤ) - b' = 0) := by
    intro n
    induction n with
    | zero => exact ⟨a, b, hab, by omega, hTab, Or.inl rfl⟩
    | succ n ih =>
      obtain ⟨a', b', h1, hn, h, hd⟩ := ih
      obtain ⟨a₂, b₂, h₂, l, hd₂⟩ := next a' b' h1 h
      refine ⟨a₂, b₂, by omega, by omega, h₂, ?_⟩
      rcases hd₂ with e | e
      · rw [e]; exact hd
      · exact Or.inr e
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference K A hA L hL hamp ((a : ℤ) - b)
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference K A hA L hL hamp 0
  obtain ⟨a', b', -, hn, h, hd⟩ := grow (N₁ + N₂)
  obtain ⟨t, ht⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  rw [ht] at h
  rcases hd with e | e
  · exact hN₁ a' b' (by omega) e t h
  · exact hN₂ a' b' (by omega) e t h

end GlobalTheory.AmpleGen
