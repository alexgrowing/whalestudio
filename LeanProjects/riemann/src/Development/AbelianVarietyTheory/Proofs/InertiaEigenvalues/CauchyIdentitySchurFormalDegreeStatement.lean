import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchy_identity_schur_formal_degree : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  first | exact @GlobalTheory.JSW.CauchyGlue.cauchy_formal | exact GlobalTheory.JSW.CauchyGlue.cauchy_formal | (intros; apply GlobalTheory.JSW.CauchyGlue.cauchy_formal <;> assumption)
