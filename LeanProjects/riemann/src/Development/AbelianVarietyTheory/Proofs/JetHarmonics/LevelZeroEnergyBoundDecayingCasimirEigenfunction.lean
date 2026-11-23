import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EnergyBoundPolynomialWeightPowCapelliEigenStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem limBd_fpm_and_fpmSh : GlobalTheory.HCXi.BesselXiIntegrable → (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd p nn (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N) ∧ (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (P : M.Par) (u u' : ℕ → ℝ) (q : KB.Pl (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') Wp Wq') (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd q nn (Formalism.FourierDecayAlt.P.CutBP2.fpmSh q f Aop p₀) Y N) := by
  intro hXi
  refine ⟨?_, ?_⟩
  · intro Wp Wq _ _ _ _ _ _ P p lam lam' cs A₀ p₀ nn f Y N h1 h2 h3 h4 h5 h6 h7
    refine GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen hXi Wp Wq Wq P p lam lam' cs A₀ p₀ 0 nn f
      (fun _ => ContinuousLinearMap.id ℂ Wq) Y N ?_ h1 h2 h3 h4 h5 h6 h7
    refine ⟨1, fun _ _ => 1, fun _ => ContinuousLinearMap.id ℂ Wq, fun _ => ?_, fun g => by simp⟩
    exact ⟨1, by simp, fun g => by simp⟩
  · intro Wp Wq _ _ _ _ _ _ Wq' _ _ _ P u u' q lam lam' cs A₀ p₀ dA nn f Aop Y N h0 h1 h2 h3 h4 h5 h6 h7
    exact GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen hXi Wp Wq' Wq (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') q lam lam' cs A₀ p₀ dA nn f Aop Y N
      h0 h1 h2 h3 h4 h5 h6 h7

end GlobalTheory
