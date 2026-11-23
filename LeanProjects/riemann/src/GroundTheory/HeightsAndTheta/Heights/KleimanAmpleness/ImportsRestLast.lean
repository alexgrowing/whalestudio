import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def RestrictGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (N : ℕ) (Ω : Type) [Field Ω] [Algebra F Ω] (x : Fin (N + 1) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (x' : Fin (N + 1) → K') (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0)
    (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
    (∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      ∃ h : aeval x f / aeval x g ∈ R, σ ⟨_, h⟩ = aeval x' f / aeval x' g) →
    ∀ (Q : Kleiman.LineBundle F x) (Q' : Kleiman.LineBundle F x') (c : ℤ) (H : Set Ω) (ρ : Ω → K') (w : Ω)
      (w' : K'), w' ≠ 0 →
      (∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I = Submodule.span (Kleiman.chartRing F x I) H) →
      (∀ I, (Q'.toSubSystem.twist (Kleiman.twistSys F x' c)).sub I =
        Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)) →
      (∀ h ∈ H, ∃ hh : h * w ∈ R, σ ⟨_, hh⟩ = ρ h * w') →
      ∃ r : Ω → K', Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
