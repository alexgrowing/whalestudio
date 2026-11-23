import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSuStatement
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormLeNormCOfEigenSum
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem energy_bound_gfPow_smul_comp_polyOp : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wf : Type) [NormedAddCommGroup Wf] [InnerProductSpace ℂ Wf] [FiniteDimensional ℂ Wf] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wf →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq →L[ℂ] Wf)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq →L[ℂ] Wf)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g))).re := by
  intro hXi Wp Wq _ _ _ _ _ _ Wf _ _ _ P p lam lam' cs A₀ p₀ dA nn f Aop Y N hA hC hI hE hgap hcl hAB hnn
    w hw hN
  have hgap' : ∀ s t, s ≠ t →
      2 * (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) < |lam' s - lam' t| := by
    intro s t hst
    have h1 := hgap s t hst
    have h2 := hcl s
    have h3 := hcl t
    have h4 : |lam s - lam t| ≤ |lam' s - lam' t| + |lam' s - lam s| + |lam' t - lam t| := by
      have e : lam s - lam t = (lam' s - lam' t) - (lam' s - lam s) + (lam' t - lam t) := by ring
      rw [e]
      have a1 := abs_add_le ((lam' s - lam' t) - (lam' s - lam s)) (lam' t - lam t)
      have a2 := abs_sub (lam' s - lam' t) (lam' s - lam s)
      linarith
    linarith
  have hes := GlobalTheory.T.capelliEigenfunction_pow_smul_comp_polyFamily_eigenSum P.k P.r Wp Wf Wq p.T.base.z p.T.base.z' lam' A₀ p₀ dA f Aop hgap'
    ⟨hC, hI⟩ hE hA
  refine GlobalTheory.levelZero_form_le_normC_of_eigen_sum hXi Wp Wq P p lam' ((2 * P.r + 2) * p₀ + dA) _ nn _ Y N hAB hes ?_ w hw hN
  intro y
  refine le_trans (Finset.prod_le_prod (fun s _ => by positivity) (fun s _ => ?_)) (hnn y)
  have h2 := hcl s
  have e : y + lam' s = (y + lam s) + (lam' s - lam s) := by ring
  have a1 := abs_add_le (y + lam s) (lam' s - lam s)
  rw [e]
  linarith

end GlobalTheory
