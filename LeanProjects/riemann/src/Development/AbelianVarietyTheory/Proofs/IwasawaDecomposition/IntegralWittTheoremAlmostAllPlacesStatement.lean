import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_witt_theorem_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y ∈ latV (M := M) (n := 1) b v, qR (Fv F v) σ J (y 0) = algebraMap F (Fv F v) β → ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y ∧ ∀ i j, ((HA.mat (Fv F v) σ J g : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v ∧ ((HA.mat (Fv F v) σ J g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v := by
  first | exact @GlobalTheory.WittIntegral.witt_integral | exact GlobalTheory.WittIntegral.witt_integral | (intros; apply GlobalTheory.WittIntegral.witt_integral <;> assumption)
