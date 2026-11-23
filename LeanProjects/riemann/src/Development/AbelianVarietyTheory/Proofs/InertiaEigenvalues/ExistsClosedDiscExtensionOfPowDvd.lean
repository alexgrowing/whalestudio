import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMap_of_pow_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap f F := by
  intro l _ A A' _ _ f u u' ρ ρ' k hρ' hdvd hk
  obtain ⟨z, hz⟩ := hdvd
  have h : ‖toDisc l u' ρ' (f u)‖ ≤ ρ := by
    rw [hz, map_mul]
    calc ‖toDisc l u' ρ' (u' ^ k) * toDisc l u' ρ' z‖
        ≤ ‖toDisc l u' ρ' (u' ^ k)‖ * ‖toDisc l u' ρ' z‖ := norm_mul_le _ _
      _ ≤ (ρ' : ℝ) ^ k * 1 :=
          mul_le_mul (norm_toDisc_pow_le k hρ') (norm_toDisc_le z) (norm_nonneg _) (by positivity)
      _ = ((ρ' ^ k : ℝ≥0) : ℝ) := by simp
      _ ≤ ρ := NNReal.coe_le_coe.2 hk
  exact ⟨Disc.map f h, isDiscMap_map f h⟩

end GlobalTheory.BSP
