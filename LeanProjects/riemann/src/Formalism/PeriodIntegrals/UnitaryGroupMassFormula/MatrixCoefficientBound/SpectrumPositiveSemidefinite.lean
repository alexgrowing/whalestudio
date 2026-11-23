import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply

open Matrix

open scoped ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

theorem spectrum_positive_semidefinite : SpecPSD := by
  intro X _ M c hM hev
  have gen : ∀ (A : Matrix X X ℂ) (hA : A.IsHermitian) (b : ℝ),
      (∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → A *ᵥ w = μ • w → ∃ r : ℝ, μ = r ∧ b ≤ r) →
      ∀ j, b ≤ hA.eigenvalues j := by
    intro A hA b h j
    have hv := hA.mulVec_eigenvectorBasis j
    have hne := hA.eigenvectorBasis.orthonormal.ne_zero j
    have key : ∀ v : X → ℂ, v ≠ 0 → A *ᵥ v = hA.eigenvalues j • v → b ≤ hA.eigenvalues j := by
      intro v hv0 hAv
      obtain ⟨r, hr, hbr⟩ := h v (hA.eigenvalues j : ℂ) hv0 (by rw [hAv]; ext i; simp)
      have hre : hA.eigenvalues j = r := by exact_mod_cast hr
      rw [hre]
      exact hbr
    exact key _ (fun h0 => hne (by ext i; simpa using congrFun h0 i)) hv
  have h1 : ((c : ℂ) • (1 : Matrix X X ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hN : ((c : ℂ) • (1 : Matrix X X ℂ) - M).IsHermitian := h1.sub hM
  have hNev : ∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → ((c : ℂ) • (1 : Matrix X X ℂ) - M) *ᵥ w = μ • w →
      ∃ r : ℝ, μ = r ∧ 0 ≤ r := by
    intro w μ hw h
    have hMw : M *ᵥ w = ((c : ℂ) - μ) • w := by
      rw [Matrix.sub_mulVec] at h
      first
        | rw [Matrix.smul_mulVec] at h
        | rw [Matrix.smul_mulVec_assoc] at h
        | simp only [Matrix.smul_mulVec_assoc] at h
      rw [Matrix.one_mulVec] at h
      rw [sub_smul, ← h]
      abel
    obtain ⟨r, hr, _, hrc⟩ := hev w ((c : ℂ) - μ) hw hMw
    refine ⟨c - r, ?_, by linarith⟩
    push_cast
    linear_combination -hr
  constructor
  · refine hM.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen M hM 0 ?_ j
    intro w μ hw h
    obtain ⟨r, hr, h0, _⟩ := hev w μ hw h
    exact ⟨r, hr, h0⟩
  · exact hN.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen _ hN 0 hNev j

end PI.GGMatBoundW
