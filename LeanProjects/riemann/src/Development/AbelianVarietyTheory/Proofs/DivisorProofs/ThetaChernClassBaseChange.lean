import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverOverIntegersExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverPullbackThetaDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantAbelianSchemeThetaDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductPolarizedThetaDegreeAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticCurveThetaStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

theorem GlobalTheory.PPAS.exists_raise_dim_ch2Omega : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ g₁ g : ℕ, g₁ ≤ g → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ P : PPAS S, P.g = g₁ → P.HasTheta → ∃ (k' : Type) (_ : CommRing k') (S' : Scheme.{0}) (p' : S' ⟶ Sp k') (_ : IsIntegral S') (P' : PPAS S') (n : ℕ), IsRegSurf p' ∧ P'.g = g ∧ P'.HasTheta ∧ 0 < n ∧ P'.degOmega p' = n * P.degOmega p ∧ ∀ a : ℝ, P.IsCh2Omega p a → P'.IsCh2Omega p' (n * a) := by
  intro hP hR g₁ g hle k _ S p _ hS P hg hT
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact ⟨k, inferInstance, S, p, inferInstance, P, 1, hS, hg, hT, one_pos, by simp, fun a ha => by simpa using ha⟩
  obtain ⟨K, _, _, E, hE1, hET⟩ := GlobalTheory.T.exists_elliptic_curve_theta
  obtain ⟨C, ⟨q⟩⟩ := GlobalTheory.T.regular_cover_over_integers_exists hR K k S p hS.toIsArithVar
  obtain ⟨P₁, h1g, h1T, h1d, h1c⟩ := GlobalTheory.T.regular_cover_pullback_theta_degree hP hR k S p hS C P hT
  have hY : IsRegSurf (C.ρ ≫ p) := C.reg
  have hQ : ∀ m : ℕ, ∃ Q : PPAS C.Y, Q.g = m + 1 ∧ Q.HasTheta ∧ Q.degOmega (C.ρ ≫ p) = 0 ∧
      Q.IsCh2Omega (C.ρ ≫ p) 0 := by
    intro m
    induction m with
    | zero =>
      obtain ⟨Q, hg', hT', hd', hc'⟩ := GlobalTheory.T.constant_abelian_scheme_theta_degree_zero hP hR K E hET k C.Y (C.ρ ≫ p) hY q
      exact ⟨Q, by rw [hg', hE1], hT', hd', hc'⟩
    | succ m ih =>
      obtain ⟨Q, hg', hT', hd', hc'⟩ := ih
      obtain ⟨Q₀, hg₀, hT₀, hd₀, hc₀⟩ := GlobalTheory.T.constant_abelian_scheme_theta_degree_zero hP hR K E hET k C.Y (C.ρ ≫ p) hY q
      obtain ⟨R, hRg, hRT, hRd, hRc⟩ := GlobalTheory.T.product_polarized_theta_degree_additive hP hR k C.Y (C.ρ ≫ p) hY Q Q₀ hT' hT₀
      exact ⟨R, by rw [hRg, hg', hg₀, hE1], hRT, by rw [hRd, hd', hd₀, add_zero], by simpa using hRc 0 0 hc' hc₀⟩
  obtain ⟨Q, hQg, hQT, hQd, hQc⟩ := hQ (g - g₁ - 1)
  obtain ⟨P', hPg, hPT, hPd, hPc⟩ := GlobalTheory.T.product_polarized_theta_degree_additive hP hR k C.Y (C.ρ ≫ p) hY P₁ Q h1T hQT
  refine ⟨k, inferInstance, C.Y, C.ρ ≫ p, inferInstance, P', C.deg, hY, ?_, hPT, C.deg_pos, ?_, ?_⟩
  · rw [hPg, h1g, hQg, hg]; omega
  · rw [hPd, h1d, hQd, add_zero]
  · intro a ha
    simpa using hPc _ 0 (h1c a ha) hQc
