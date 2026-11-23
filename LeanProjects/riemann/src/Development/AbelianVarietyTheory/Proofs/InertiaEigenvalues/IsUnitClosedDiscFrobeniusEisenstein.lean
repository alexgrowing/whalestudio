import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadiusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isUnit_toDisc_frobS_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsUnit (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := by
  intro l hl K bk
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hl0 : (0 : ℝ) < l := by linarith
  have hE : ‖toDisc l (X : bk.S) bk.ρ₀ bk.E‖ ≤ (l : ℝ)⁻¹ := (GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk bk.S (RingHom.id _)).2.2.2
  obtain ⟨v, hv⟩ := bk.isUnit_δ
  have hφ : frobS l bk.a bk.E = bk.E ^ l + (l : bk.S) * (v : bk.S) := by
    rw [hv]; exact (deltaS l bk.a).φ_eq bk.E
  set t := toDisc l (X : bk.S) bk.ρ₀ with ht
  set i : Disc l (X : bk.S) bk.ρ₀ := ofPre l (X : bk.S) bk.ρ₀ (IsLocalization.Away.invSelf (l : bk.S)) with hi
  have hLi : (l : Disc l (X : bk.S) bk.ρ₀) * i = 1 := by
    rw [hi, ← map_natCast (ofPre l (X : bk.S) bk.ρ₀), ← map_mul,
      ← map_natCast (algebraMap bk.S (PreDisc l (X : bk.S) bk.ρ₀)), IsLocalization.Away.mul_invSelf, map_one]
  have hni : ‖i‖ ≤ l := by
    rw [hi, norm_ofPre]
    exact gauge_le l _ _ hl0 (Submodule.subset_span ⟨0, 0, 1, by simp, by simp⟩)
  have hw : t v * t ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  set z := i * t ↑v⁻¹ * t bk.E ^ l with hz
  have hnz : ‖z‖ < 1 := by
    have h1 : ‖t bk.E ^ l‖ ≤ (l : ℝ)⁻¹ ^ l :=
      (norm_pow_le' _ hl.out.pos).trans (pow_le_pow_left₀ (norm_nonneg _) hE l)
    have h2 : (l : ℝ)⁻¹ ^ l ≤ (l : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by linarith)) (by exact_mod_cast hl.out.two_le)
    calc ‖z‖ ≤ ‖i‖ * ‖t ↑v⁻¹‖ * ‖t bk.E ^ l‖ := by
            rw [hz]; exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (l : ℝ) * 1 * (l : ℝ)⁻¹ ^ 2 := by
            gcongr
            · exact norm_toDisc_le _
            · exact h1.trans h2
      _ = (l : ℝ)⁻¹ := by field_simp
      _ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have key : t (frobS l bk.a bk.E) = (l : Disc l (X : bk.S) bk.ρ₀) * t v * (1 - (-z)) := by
    rw [hφ, map_add, map_mul, map_pow, map_natCast, hz]
    linear_combination (-(t bk.E ^ l) * (t v * t ↑v⁻¹)) * hLi + (-(t bk.E ^ l)) * hw
  rw [key]
  exact ((isUnit_l_disc l (X : bk.S) bk.ρ₀).mul ((Units.isUnit v).map t)).mul
    ⟨Units.oneSub (-z) (by rwa [norm_neg]), rfl⟩

end GlobalTheory.BSP
