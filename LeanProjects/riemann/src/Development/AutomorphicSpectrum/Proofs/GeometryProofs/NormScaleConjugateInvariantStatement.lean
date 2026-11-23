import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormScaleConjugateInvariant
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_scale_conjugate_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (M : ℕ) (f g : MRing ι) (dg : K → ℕ) (κ : (F →+* ℂ) → ℝ), OverInt y φ → 0 < M → IsMultiHomog g dg → g ∉ mCoordIdeal y → IsConjInvariantH A → (∀ σ, 0 < κ σ) → (∀ σ z, PtOver y φ σ z → ‖evC z f‖ = (κ σ * A.h z) ^ M * ‖evC z g‖) → ∀ σ, κ (ComplexEmbedding.conjugate σ) = κ σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.kappa_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.kappa_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.kappa_conj <;> assumption)
