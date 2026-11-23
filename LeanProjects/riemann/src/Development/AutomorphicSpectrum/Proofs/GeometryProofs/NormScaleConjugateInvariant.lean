import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsComplexPointNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem kappa_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type)
    [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (M : ℕ) (f g : MRing ι) (dg : K → ℕ)
    (κ : (F →+* ℂ) → ℝ), OverInt y φ → 0 < M → IsMultiHomog g dg → g ∉ mCoordIdeal y → IsConjInvariantH A →
    (∀ σ, 0 < κ σ) → (∀ σ z, PtOver y φ σ z → ‖evC z f‖ = (κ σ * A.h z) ^ M * ‖evC z g‖) →
    ∀ σ, κ (ComplexEmbedding.conjugate σ) = κ σ := by
  intro K _ ι _ Ω _ F _ _ y φ A M f g dg κ hO hM hg hgy hA hκ hN σ
  obtain ⟨z, hz, hgz⟩ := GlobalTheory.T.exists_complex_point_nonvanishing K ι Ω F y φ σ g dg hO hg hgy
  have h1 := hN σ z hz
  have h2 := hN _ _ (ptOver_conj K ι Ω F y φ σ z hz)
  rw [evC_conj, evC_conj, hA z, RCLike.norm_conj, RCLike.norm_conj] at h2
  have hgn : ‖evC z g‖ ≠ 0 := norm_ne_zero_iff.2 hgz
  have hh : 0 < A.h z := A.pos z hz.1.1
  have h3 : (κ (ComplexEmbedding.conjugate σ) * A.h z) ^ M = (κ σ * A.h z) ^ M :=
    mul_right_cancel₀ hgn (h2.symm.trans h1)
  have h4 := (pow_left_inj₀ (mul_pos (hκ _) hh).le (mul_pos (hκ _) hh).le hM.ne').1 h3
  exact mul_right_cancel₀ hh.ne' h4

end GlobalTheory.CompanionTheory.Ar.Flat
