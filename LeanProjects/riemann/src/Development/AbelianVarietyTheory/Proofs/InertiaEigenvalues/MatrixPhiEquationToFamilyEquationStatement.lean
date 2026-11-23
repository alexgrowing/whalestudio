import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixPhiEquationToFamilyEquation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_phi_equation_to_family_equation : ∀ (R C : Type) [CommRing R] [CommRing C] (i : R →+* C) (φ : C → C) (e e' : R), Associated e e' → ∀ (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') R) (Q Q' : Matrix (Fin d) (Fin d) R), Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R) → ∀ Δ : Matrix (Fin d') (Fin d) C, i e' ^ a • (P.map i * Δ.map φ) = i e ^ a' • (Δ * Q.map i) → ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → R), ∀ j : Fin d' × Fin d, i e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * i (c k j) := by
  first | exact @GlobalTheory.BSP.matrix_phi_eq_family | exact GlobalTheory.BSP.matrix_phi_eq_family | (intros; apply GlobalTheory.BSP.matrix_phi_eq_family <;> assumption)
