import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfEqualTypes
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HerGenC
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliEigenfunction_pointwiseBound_of_equalTypes : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → (n₀ = 30 * (P.r + 1) ^ 2 + 6 ∧ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) ∧ ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes.thmBp_eig_eq | exact GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes.thmBp_eig_eq | (intros; apply GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes.thmBp_eig_eq <;> assumption)
