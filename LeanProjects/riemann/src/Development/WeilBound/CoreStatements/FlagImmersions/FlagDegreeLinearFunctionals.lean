import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Formalism.DegreeFormula.PointDegree.PowSum

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

noncomputable def pa_degFlL (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) : RP Ψ N →ₗ[ℝ] ℝ where
  toFun F := degFl F
  map_add' P Q := Formalism.DegreeFormula.PPowSum.degFl_add P Q
  map_smul' c P := by
    rw [smul_eq_C_mul]
    exact Formalism.DegreeFormula.PPowSum.degFl_C_mul c P

theorem pa_degFlL_apply {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (F : RP Ψ N) :
    pa_degFlL Ψ N F = degFl F := rfl

theorem degFl_Sh_Tot_linear_and_degFl_eq_zero_off_dim : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = degFl F) ∧ (∀ (j : ℕ) (τ : Ψ), ∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = Sh j τ F) ∧ (∀ τ : Ψ, ∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = Tot τ F) ∧ ∀ (d : ℕ) (F : RP Ψ N), F.IsHomogeneous d → d ≠ dimFl Ψ N → degFl F = 0 := by
  intro Ψ _ _ N
  refine ⟨⟨pa_degFlL Ψ N, fun F => pa_degFlL_apply F⟩, ?_, ?_, ?_⟩
  · intro j τ
    refine ⟨(pa_degFlL Ψ N).comp (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
      ((pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)) : RP Ψ N →ₗ[ℝ] RP Ψ N)), fun F => ?_⟩
    rw [LinearMap.comp_apply, pa_degFlL_apply, LinearMap.sum_apply]
    rfl
  · intro τ
    refine ⟨(pa_degFlL Ψ N).comp (∑ i : Fin N,
      ((pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)) : RP Ψ N →ₗ[ℝ] RP Ψ N)), fun F => ?_⟩
    rw [LinearMap.comp_apply, pa_degFlL_apply, LinearMap.sum_apply]
    rfl
  · intro d F hF hd
    exact Formalism.DegreeFormula.PPowSum.degFlHomog Ψ N d F hF hd

end RootFieldNumerics
