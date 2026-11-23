import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingPairSectionsNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.MpDivTwist

theorem mem_Bl_of_mul_pow_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c : ℕ), GenAt P c → ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N (-c) → f * s ^ m ∈ P.Bl N (m - c) 2 → f ∈ P.Bl N (-c) (Real.exp (δ * N + C * m + C)) := by
  intro k _ X _ p D hX P c hc s hs hs0 δ hδ

  obtain ⟨n, v, ρ₁, hρ₁, hv, hcov⟩ := GlobalTheory.T.generatingPairSections_norm_bounds k X p D hX P c hc

  obtain ⟨ρ₂, hρ₂, hmax⟩ := GlobalTheory.T.arith_global_maximum_principle_off_divisor k X p D hX P s hs hs0 δ hδ
  have hnu0 : ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (g : X.functionField), 0 ≤ P.nu a b σ y g := by
    intro a b σ y g
    unfold Pair.nu
    positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, Real.exp A = ρ₂⁻¹ := ⟨_, Real.exp_log (inv_pos.2 hρ₂)⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, Real.exp B = 2 * ρ₁⁻¹ * ρ₁⁻¹ := ⟨_, Real.exp_log (by positivity)⟩
  refine ⟨|A| + |B|, by positivity, ?_⟩
  intro N m f hf hfs
  obtain ⟨hsm, hsmnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs m
  obtain ⟨-, hfsnu⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P (N : ℤ) (-(c : ℤ)) ((m : ℤ) * 0) ((m : ℤ) * 1) f (s ^ m) hf hsm

  have key : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ₂ ≤ P.nu 0 1 σ y s → P.nu N (-c) σ y f ≤ 2 * ρ₂⁻¹ ^ m := by
    intro σ y hy
    have h1 := hfsnu σ y
    rw [hsmnu σ y] at h1
    have h2 : P.nu ((N : ℤ) + (m : ℤ) * 0) (-(c : ℤ) + (m : ℤ) * 1) σ y (f * s ^ m) ≤ 2 := by
      have e1 : ((N : ℤ) + (m : ℤ) * 0) = N := by ring
      have e2 : (-(c : ℤ) + (m : ℤ) * 1) = (m : ℤ) - c := by ring
      rw [e1, e2]
      exact hfs.2 σ y
    rw [h1] at h2
    have h3 : P.nu N (-c) σ y f * ρ₂ ^ m ≤ 2 := by
      calc P.nu N (-c) σ y f * ρ₂ ^ m ≤ P.nu N (-c) σ y f * P.nu 0 1 σ y s ^ m := by
            gcongr
            exact hnu0 _ _ _ _ _
        _ ≤ 2 := h2
    calc P.nu N (-c) σ y f = P.nu N (-c) σ y f * ρ₂ ^ m * ρ₂⁻¹ ^ m := by
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ₂.ne', one_pow, mul_one]
      _ ≤ 2 * ρ₂⁻¹ ^ m := by gcongr

  have hprod : ∀ i, ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu N (-c) σ y f * P.nu 0 c σ y (v i) ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) := by
    intro i
    obtain ⟨hfv, hfvnu⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P (N : ℤ) (-(c : ℤ)) 0 (c : ℤ) f (v i) hf (hv i).1
    have e1 : ((N : ℤ) + 0) = N := by ring
    have e2 : (-(c : ℤ) + c) = 0 := by ring
    rw [e1, e2] at hfv hfvnu
    have hb := hmax N (f * v i) (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) hfv (fun σ y hy => by
      rw [hfvnu σ y]
      exact mul_le_mul (key σ y hy) ((hv i).2 σ y) (hnu0 _ _ _ _ _) (by positivity))
    intro σ y
    rw [← hfvnu σ y]
    exact hb.2 σ y
  refine ⟨hf, fun σ y => ?_⟩
  obtain ⟨i, hi⟩ := hcov σ y
  have h4 : P.nu N (-c) σ y f * ρ₁ ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) :=
    calc P.nu N (-c) σ y f * ρ₁ ≤ P.nu N (-c) σ y f * P.nu 0 c σ y (v i) := by
          gcongr
          exact hnu0 _ _ _ _ _
      _ ≤ _ := hprod i σ y
  have hAC : A ≤ |A| + |B| := by
    have := le_abs_self A
    have := abs_nonneg B
    linarith
  have hBC : B ≤ |A| + |B| := by
    have := le_abs_self B
    have := abs_nonneg A
    linarith
  calc P.nu N (-c) σ y f = P.nu N (-c) σ y f * ρ₁ * ρ₁⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hρ₁.ne', mul_one]
    _ ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) * ρ₁⁻¹ := by gcongr
    _ = Real.exp (δ * N) * ρ₂⁻¹ ^ m * (2 * ρ₁⁻¹ * ρ₁⁻¹) := by ring
    _ = Real.exp (δ * N) * Real.exp (m * A) * Real.exp B := by rw [Real.exp_nat_mul, hA, hB]
    _ ≤ Real.exp (δ * N) * Real.exp (m * (|A| + |B|)) * Real.exp (|A| + |B|) := by
        gcongr
    _ = Real.exp (δ * N + (|A| + |B|) * m + (|A| + |B|)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end GlobalTheory.HSNef.MpDivTwist
