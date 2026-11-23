import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HerGenC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffDominatedOfHCXiStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfDifferentTypStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfEqualTypesStatement
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.BpEigen

theorem pointwise_bound_mono {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {b C C' : ℝ} {n₀ p₀ : ℕ}
    (hb : 1 ≤ b) (hC : C ≤ C') (h : TBB.ThmBpAt p f b C n₀ p₀) : TBB.ThmBpAt p f b C' n₀ p₀ := by
  intro γ hγ hG
  refine (h γ hγ hG).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 hG.le) _)
  refine Real.rpow_le_rpow_of_exponent_le hb ?_
  exact mul_le_mul_of_nonneg_right hC (by positivity)

theorem pointwise_bound_eigenfunction : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → Cases P n₀ → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP C C₃ C₀ hC hC₃ hC₀
  have hN := GlobalTheory.T.topDensity_cutoff_dominated_of_HC_xi hX
  obtain ⟨D₁, E₁, h₁⟩ := GlobalTheory.T.capelliEigenfunction_pointwiseBound_of_differentTypes hX hP hN C C₃ C₀ hC hC₃ hC₀
  obtain ⟨D₂, E₂, h₂⟩ := GlobalTheory.T.capelliEigenfunction_pointwiseBound_of_equalTypes hX hP hN C C₃ C₀ hC hC₃ hC₀
  refine ⟨max D₁ D₂, max E₁ E₂, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b c A₀ n₀ p₀ lam lam' hS hc h3 hp hE hA hl hR
  have key : ∀ E : ℝ, E ≤ max E₁ E₂ → E * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) := by
    intro E hE'
    refine le_trans ?_ hA
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE' (by positivity)) (by positivity)
  rcases hc with hc | hc
  · have hb : 1 ≤ b := by
      obtain ⟨-, l, hl', -⟩ := hc
      obtain ⟨a1, a2, -⟩ := hS.1 l hl'
      linarith
    exact pointwise_bound_mono hb (le_max_left _ _)
      (h₁ P Wp Wq p f b c A₀ n₀ p₀ lam lam' hS hc h3 hp hE (key _ (le_max_left _ _)) hl hR)
  · have hb : 1 ≤ b := by
      obtain ⟨-, -, l, hl1, hl2, -⟩ := hc
      obtain ⟨a1, a2, -⟩ := hS.1 l (Finset.mem_Icc.2 ⟨hl1, hl2.le⟩)
      linarith
    exact pointwise_bound_mono hb (le_max_right _ _)
      (h₂ P Wp Wq p f b c A₀ n₀ p₀ lam lam' hS hc h3 hp hE (key _ (le_max_right _ _)) hl hR)

end GlobalTheory.BpEigen
