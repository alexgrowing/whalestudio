import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShear
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_extending_isotropic_shear : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ), 0 < N → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' → ∀ t : Z →ₗ[𝓞 E] D.La,
    (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) → (∀ z z' : Z, D.EF (t z) (t z') = 0) →
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧ ∀ z : Z, g z = t z := by
  first | exact @GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | exact GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | (intros; apply GlobalTheory.LowFilt.IsOpp.exists_isometry_extend <;> assumption)
