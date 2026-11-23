import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PadicPolys

theorem minpoly_coeff_bdd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1),
      f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ),
        ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  intro p _ G K' f' hf β
  obtain ⟨k0, hk0⟩ := GlobalTheory.AtPBd.main p G 1 K' f' one_pos hf
  set R : ℝ := (p : ℝ) ^ k0 with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  refine ⟨max (R * R) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y h hy φ k
  have hnrm : IsNrm G 1 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h := by
    show nrmG (sigG G 1) 1 _ = _
    simp [nrmG]
    rfl
  obtain ⟨hs, -, hrt, hrti⟩ := hk0 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h 1 hnrm (by simpa using hy)
  set yC : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyC
  have hint : IsIntegral G.F yC := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly G.F yC).Monic := minpoly.monic hint
  have hsn : ‖(((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)‖ ≤ R := by
    rw [← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact hs
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hroot : ∀ μ ∈ ((minpoly G.F yC).map φ).roots, ‖μ‖ ≤ R * R := by
    intro μ hμ
    have hμ' : ((minpoly G.F yC).map φ).IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
    rcases GlobalTheory.GlobEig.liesOver_or_conj G φ with hφ | hφ
    · obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G φ hφ yC μ hμ'
      rw [← hν]
      exact (hrt i ν hνr).trans (le_mul_of_one_le_left (by linarith) hR1)
    · have h2 := GlobalTheory.GlobEig.isRoot_minpoly_sh G yC φ μ hμ'
      obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G _ hφ (sh G yC) μ h2
      have h3 := GlobalTheory.GlobEig.isRoot_inv G i β (y : G.Cˣ × ℚˣ).1 (y : G.Cˣ × ℚˣ).2 y.2.1 ν hνr
      have h4 := hrti i _ h3
      rw [← hν]
      have e : ν = ν * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)⁻¹ * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) := by
        field_simp
      rw [e, norm_mul]
      exact mul_le_mul h4 hsn (norm_nonneg _) (by linarith)
  have hdeg : (minpoly G.F yC).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le yC
  rw [← Polynomial.coeff_map]
  exact Polynomial.coeff_bdd_of_roots_le φ hmon (IsAlgClosed.splits _) hdeg hroot k

end GlobalTheory.LKCx.PadicPolys
