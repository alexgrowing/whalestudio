import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_isLowUnitH_of_isDSHpk {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε mu σ) : ∃ w, ‖w‖ = 1 ∧ PI.UpqRep.IsLowUnitH k r ε mu σ w := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hn : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
    rw [norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, hn, P, hP, hn, ?_⟩
  exact Submodule.smul_mem _ _ (le_sSup (s := {S | PI.UpqRep.IsKTypeOf ε (fun g => σ (P⁻¹ * g * P))
    (PI.UpqRep.lowK ε mu) S}) hS hvS)

theorem rep_basic_of_isDS : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  intro hK k r ε mu R hR
  obtain ⟨hmu, hσ⟩ := hR
  obtain ⟨h1, hunit⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hσ
  have hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v) := by
    intro g hg h hh v
    rw [Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hg hh]; rfl
  have hone : ∀ v, R.σ 1 v = v := fun v => by rw [h1]; rfl
  have hsm : ∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm := fun g hg v hv =>
    Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hσ hv hg
  refine ⟨hmul, hone, ?_, hsm, ?_, ?_, ?_, ?_, fun v => Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ v⟩
  · intro g hg
    exact (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 (hunit g hg)
  · have : R.TK ≤ R.smSub := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, hg, v₀, hv₀, rfl⟩
      exact hsm g hg v₀ (hK k r ε mu R.H R.σ hmu hσ v₀ hv₀)
    exact fun v hv => this hv
  · intro g hg
    have : R.TK ≤ R.TK.comap ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, hh, v₀, hv₀, rfl⟩
      exact Submodule.subset_span ⟨g * h, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg hh, v₀, hv₀, (hmul g hg h hh v₀).symm⟩
    exact fun v hv => this hv
  · intro v hv
    refine Submodule.subset_span ⟨1, ?_, v, hv, (hone v).symm⟩
    show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  · obtain ⟨w, hw, hlow⟩ := exists_isLowUnitH_of_isDSHpk hσ
    exact ⟨w, hw, PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow, hlow⟩

end GlobalTheory
