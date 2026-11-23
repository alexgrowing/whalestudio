import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionKltPairSeparationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingSectionOfIsolatedNonKltPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hlc hNamp hnum
    hx₁ hx₂ hne hh hvol hsum
  set S : ℚ := ∑ e ∈ Finset.Icc 1 n, h e with hS
  set ε : ℚ := (ρ - S) / (n + 1) with hε
  have hn1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hεpos : 0 < ε := div_pos (by linarith) hn1
  have h1 : ((n : ℚ) + 1) * ε = ρ - S := by rw [hε]; field_simp
  have hsplit : ∑ e ∈ Finset.Icc 1 n, (h e + ε) = S + n * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp [hS]
  obtain ⟨D, d, hd, hQ, hcase⟩ := GlobalTheory.T.twoPoint_induction_kltPair_separation hP hNV hNef X p n hproj hdim Δ m G N ε h x₁ x₂
    hΔ hklt hm hlc hNamp hx₁ hx₂ hne hh hvol hεpos
  have hdρ : d < ρ := by
    have h2 : (n : ℚ) * ε + ε = ρ - S := by rw [← h1]; ring
    linarith
  rcases hcase with ⟨hlc1, hnk2⟩ | ⟨hlc2, hnk1⟩
  · obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₁ x₂ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₁ hne hlc1 hnk2
    exact ⟨s, Or.inl ⟨hs1, hs2⟩⟩
  · obtain ⟨s, hs2, hs1⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₂ x₁ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₂ (Ne.symm hne) hlc2 hnk1
    exact ⟨s, Or.inr ⟨hs2, hs1⟩⟩
