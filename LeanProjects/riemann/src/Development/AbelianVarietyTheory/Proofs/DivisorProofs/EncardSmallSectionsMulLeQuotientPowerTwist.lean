import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardMulLeOfQuotEmbed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMemTwistedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem encard_mul_le_at_level_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, ∀ (N m : ℕ), (P.Bl N (m - c) 1).encard * (P.Bl 0 (b * N - c) 1).encard ≤ {f | f ∈ P.H N (-c) ∧ f * s ^ m ∈ P.Bl N (m - c) 2}.encard * (P.Bl 0 (b * N + m - c) 2).encard := by
  intro k _ X _ p D hD P b s t hG c N m
  have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hD P N ((m : ℤ) - c) 1
  have bf := GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P
  have hmul := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P
  have hpow := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P
  have hreg := GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem_twisted k X p D hD P b s t hG c N m
  have nu_nn : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f := by
    intro a c σ y f
    unfold Pair.nu
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hsm : s ^ m ≠ 0 := pow_ne_zero m hG.s_ne
  obtain ⟨hsH, hsν⟩ := hpow 0 1 s hG.s_mem.1 m
  obtain ⟨htH, htν⟩ := hpow (-1) b t hG.t_mem.1 N
  have hsν1 : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu ((m : ℤ) * 0) ((m : ℤ) * 1) σ y (s ^ m) ≤ 1 := by
    intro σ y
    rw [hsν]
    exact pow_le_one₀ (nu_nn _ _ _ _ _) (hG.s_mem.2 σ y)
  have htν1 : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu ((N : ℤ) * -1) ((N : ℤ) * b) σ y (t ^ N) ≤ 1 := by
    intro σ y
    rw [htν]
    exact pow_le_one₀ (nu_nn _ _ _ _ _) (hG.t_mem.2 σ y)
  let Ts : X.functionField →+ X.functionField := AddMonoidHom.mulRight (s ^ m)
  let Tt : X.functionField →+ X.functionField := AddMonoidHom.mulRight (t ^ N)
  let Λ₀ : AddSubgroup X.functionField := (P.H N (-(c : ℤ))).map Ts
  let Λ₀' : AddSubgroup X.functionField := (P.H 0 ((b : ℤ) * N - c)).map Ts

  have hT : ∀ u ∈ P.Bl N ((m : ℤ) - c) 1, Tt u ∈ P.Bl 0 ((b : ℤ) * N + m - c) 1 := by
    intro u hu
    obtain ⟨hH, hν⟩ := hmul _ _ _ _ u (t ^ N) hu.1 htH
    have e1 : (N : ℤ) + N * -1 = 0 := by ring
    have e2 : ((m : ℤ) - c) + N * b = b * N + m - c := by ring
    rw [e1, e2] at hH hν
    refine ⟨hH, fun σ y => ?_⟩
    show P.nu 0 ((b : ℤ) * N + m - c) σ y (u * t ^ N) ≤ 1
    rw [hν]
    have := mul_le_mul (hu.2 σ y) (htν1 σ y) (nu_nn _ _ _ _ _) zero_le_one
    simpa using this

  have hpull : ∀ u ∈ P.H N ((m : ℤ) - c), Tt u ∈ Λ₀' → u ∈ Λ₀ := by
    intro u hu hmem
    obtain ⟨g, hg, hgu⟩ := AddSubgroup.mem_map.mp hmem
    have hgu' : g * s ^ m = u * t ^ N := hgu
    have hdiv : u * t ^ N / s ^ m ∈ P.H 0 ((b : ℤ) * N - c) := by
      rw [← hgu', mul_div_assoc, div_self hsm, mul_one]; exact hg
    have := hreg u hu hdiv
    refine AddSubgroup.mem_map.mpr ⟨u / s ^ m, this, ?_⟩
    show u / s ^ m * s ^ m = u
    exact div_mul_cancel₀ u hsm
  have key := GlobalTheory.VolBr.encard_mul_le_of_quot_embed X.functionField (P.H N ((m : ℤ) - c))
    (P.H 0 ((b : ℤ) * N + m - c)) Λ₀ Λ₀' (P.Bl N ((m : ℤ) - c)) (P.Bl 0 ((b : ℤ) * N + m - c)) Tt (bf _ _) (bf _ _)
    hT hpull hfin

  have hA : (P.Bl 0 ((b : ℤ) * N - c) 1).encard ≤
      (P.Bl 0 ((b : ℤ) * N + m - c) 1 ∩ (Λ₀' : Set X.functionField)).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun f => f * s ^ m) ?_ ?_
    · intro f hf
      obtain ⟨hH, hν⟩ := hmul _ _ _ _ f (s ^ m) hf.1 hsH
      have e1 : (0 : ℤ) + m * 0 = 0 := by ring
      have e2 : ((b : ℤ) * N - c) + m * 1 = b * N + m - c := by ring
      rw [e1, e2] at hH hν
      refine ⟨⟨hH, fun σ y => ?_⟩, AddSubgroup.mem_map.mpr ⟨f, hf.1, rfl⟩⟩
      rw [hν]
      have := mul_le_mul (hf.2 σ y) (hsν1 σ y) (nu_nn _ _ _ _ _) zero_le_one
      simpa using this
    · intro f _ g _ h
      exact mul_right_cancel₀ hsm h

  have hB : (P.Bl N ((m : ℤ) - c) 2 ∩ (Λ₀ : Set X.functionField)).encard ≤
      {f | f ∈ P.H N (-(c : ℤ)) ∧ f * s ^ m ∈ P.Bl N ((m : ℤ) - c) 2}.encard := by
    refine le_trans (Set.encard_le_encard
      (t := (fun f => f * s ^ m) '' {f | f ∈ P.H N (-(c : ℤ)) ∧ f * s ^ m ∈ P.Bl N ((m : ℤ) - c) 2}) ?_)
      (Set.encard_image_le _ _)
    rintro x ⟨hx, hx0⟩
    obtain ⟨f, hf, rfl⟩ := AddSubgroup.mem_map.mp hx0
    exact ⟨f, ⟨hf, hx⟩, rfl⟩
  calc (P.Bl N ((m : ℤ) - c) 1).encard * (P.Bl 0 ((b : ℤ) * N - c) 1).encard
      ≤ (P.Bl N ((m : ℤ) - c) 1).encard *
          (P.Bl 0 ((b : ℤ) * N + m - c) 1 ∩ (Λ₀' : Set X.functionField)).encard := mul_le_mul' le_rfl hA
    _ ≤ (P.Bl N ((m : ℤ) - c) 2 ∩ (Λ₀ : Set X.functionField)).encard * (P.Bl 0 ((b : ℤ) * N + m - c) 2).encard := key
    _ ≤ {f | f ∈ P.H N (-(c : ℤ)) ∧ f * s ^ m ∈ P.Bl N ((m : ℤ) - c) 2}.encard *
          (P.Bl 0 ((b : ℤ) * N + m - c) 2).encard := mul_le_mul' hB le_rfl

end GlobalTheory.HSNef
