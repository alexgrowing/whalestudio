import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardMulLeOfQuotEmbed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMemStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_at_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ),
    (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤
      {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  intro k _ X _ p D hX P b s t hg N m hfin

  have hnu : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f := by
    intro a c σ y f
    unfold Pair.nu
    positivity
  have hs0 : s ^ m ≠ 0 := pow_ne_zero _ hg.s_ne

  obtain ⟨hsH, hsnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hg.s_mem.1 m
  obtain ⟨htH, htnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t hg.t_mem.1 N
  have hsle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑m * 0) (↑m * 1) σ y (s ^ m) ≤ 1 := by
    intro σ y
    rw [hsnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.s_mem.2 σ y)
  have htle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑N * (-1)) (↑N * ↑b) σ y (t ^ N) ≤ 1 := by
    intro σ y
    rw [htnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.t_mem.2 σ y)

  let Λ₀ : AddSubgroup X.functionField := (P.H N 0).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  let Λ₀' : AddSubgroup X.functionField := (P.H 0 (b * N)).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  have key := GlobalTheory.VolBr.encard_mul_le_of_quot_embed X.functionField (P.H N m) (P.H 0 (b * N + m)) Λ₀ Λ₀'
    (P.Bl N m) (P.Bl 0 (b * N + m)) (AddMonoidHom.mulRight (t ^ N))
    (GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P N m) (GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P 0 (b * N + m)) ?_ ?_ hfin
  rotate_left
  ·
    intro u hu
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N m (↑N * (-1)) (↑N * ↑b) u (t ^ N) hu.1 htH
    have e1 : (N : ℤ) + ↑N * (-1) = 0 := by ring
    have e2 : (m : ℤ) + ↑N * ↑b = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    simp only [AddMonoidHom.coe_mulRight]
    rw [hn]
    exact mul_le_one₀ (hu.2 σ y) (hnu _ _ _ _ _) (htle σ y)
  ·
    intro u hu hT
    simp only [Λ₀, Λ₀', AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight] at hT ⊢
    rw [← div_eq_mul_inv] at hT ⊢
    exact GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem k X p D hX P b s t hg N m u hu hT

  have hE : (P.Bl 0 (b * N) 1).encard ≤ (P.Bl 0 (b * N + m) 1 ∩ (Λ₀' : Set X.functionField)).encard := by
    rw [← (mul_left_injective₀ hs0).injOn.encard_image]
    apply Set.encard_le_encard
    rintro _ ⟨g, hg', rfl⟩
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P 0 (↑b * ↑N) (↑m * 0) (↑m * 1) g (s ^ m) hg'.1 hsH
    have e1 : (0 : ℤ) + ↑m * 0 = 0 := by ring
    have e2 : (↑b * ↑N : ℤ) + ↑m * 1 = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨⟨hH, fun σ y => ?_⟩, ?_⟩
    · rw [hn]
      exact mul_le_one₀ (hg'.2 σ y) (hnu _ _ _ _ _) (hsle σ y)
    · show g * s ^ m * (s ^ m)⁻¹ ∈ P.H 0 (↑b * ↑N)
      rw [mul_inv_cancel_right₀ hs0]
      exact hg'.1

  have hB : (P.Bl N m 2 ∩ (Λ₀ : Set X.functionField)) =
      (fun f => f * s ^ m) '' {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2} := by
    ext u
    constructor
    · rintro ⟨hu, hu0⟩
      refine ⟨u * (s ^ m)⁻¹, ⟨hu0, ?_⟩, ?_⟩
      · rw [inv_mul_cancel_right₀ hs0]
        exact hu
      · exact inv_mul_cancel_right₀ hs0 u
    · rintro ⟨f, ⟨hf, hfs⟩, rfl⟩
      refine ⟨hfs, ?_⟩
      show f * s ^ m * (s ^ m)⁻¹ ∈ P.H N 0
      rw [mul_inv_cancel_right₀ hs0]
      exact hf
  rw [hB, (mul_left_injective₀ hs0).injOn.encard_image] at key
  refine le_trans ?_ key
  gcongr

end GlobalTheory.VolBr
