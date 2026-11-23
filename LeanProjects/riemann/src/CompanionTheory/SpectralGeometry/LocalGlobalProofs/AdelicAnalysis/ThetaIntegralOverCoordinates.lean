import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueNonnegativeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceForm
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.PullCoord

theorem lintegral_thetaMeas_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (S : Set (Fin M × Fin d → F)) (T : Set (Fin 1 → Fin M → E)), (∀ x, ofF b x ∈ T ↔ x ∈ S) → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 T) = ∫⁻ ω, ∑' x : S, Φ (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b μ 𝓕 hμ h𝓕 S T hST Φ hΦ
  rw [GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ 𝓕 hμ h𝓕 1 T Φ hΦ]
  have hb := RatCoord.ofF_bijective (M := M) b
  let e : S ≃ T := Equiv.ofBijective (fun x => ⟨ofF b x.1, (hST x.1).2 x.2⟩) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (hb.1 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx⟩ := hb.2 y.1
      exact ⟨⟨x, (hST x).1 (hx ▸ y.2)⟩, Subtype.ext hx⟩)
  have hsum : ∀ h : HA (AF F) σ J,
      ∑' X : T, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))
        = ∑' x : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (ofF b x.1))) := fun h =>
    (e.tsum_eq (fun X : T =>
      Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E))))).symm
  simp only [hsum, prH, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.SW.BB.PullCoord
