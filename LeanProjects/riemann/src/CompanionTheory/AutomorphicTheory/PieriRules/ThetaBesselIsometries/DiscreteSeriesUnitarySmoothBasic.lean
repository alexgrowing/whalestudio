import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_isLowUnitH_of_isDSHpk {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε mu σ) : ∃ w, ‖w‖ = 1 ∧ PI.UpqRep.IsLowUnitH k r ε mu σ w := by
  unfold PI.UpqRep.IsDSHpk at hσ
  obtain ⟨P, hP, hds⟩ := hσ
  unfold PI.UpqRep.IsDS at hds
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hds
  have hS' := hS
  unfold PI.UpqRep.IsKTypeOf at hS'
  obtain ⟨v, hvS, hv0, -⟩ := hS'.2.2.2.1
  have hle : S ≤ PI.UpqRep.lowKSub ε mu (fun g => σ (P⁻¹ * g * P)) := le_sSup hS
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, norm_smul_inv_norm hv0, ?_⟩
  unfold PI.UpqRep.IsLowUnitH PI.UpqRep.IsLowUnit
  exact ⟨P, hP, norm_smul_inv_norm hv0, Submodule.smul_mem _ _ (hle hvS)⟩

theorem rep_basic_of_isDS : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  intro hK k r ε mu R hDG
  have hds : PI.UpqRep.IsDSHpk k r ε mu R.σ := hDG.ds
  have hc : PI.UpqRep.IsHCParam mu := hDG.hc
  have toPI : ∀ g, g ∈ GG k r → g ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r) := by
    intro g hg
    rw [← Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq]
    exact hg
  have ofPI : ∀ g, g ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r) → g ∈ GG k r := by
    intro g hg
    show g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
    rw [Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq]
    exact hg
  have hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v) := by
    intro g hg h hh v
    have e := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds (toPI g hg) (toPI h hh)
    exact congrArg (fun T => T v) e
  have hone : ∀ v, R.σ 1 v = v := by
    intro v
    have e := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hds).1
    simpa using congrArg (fun T : R.H →L[ℂ] R.H => T v) e
  have hsmooth : ∀ v, R.KFin v → v ∈ R.sm := fun v hv => hK k r ε mu R.H R.σ hc hds v hv
  have hsm : ∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm := by
    intro g hg v hv
    exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hds hv (toPI g hg)
  refine ⟨hmul, hone, ?_, hsm, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg v w
    have hinv := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    have e1 := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_inner hds hg (R.σ g v) w
    have e2 := hmul g⁻¹ hinv.1 g hg v
    rw [hinv.2.2, hone] at e2
    rw [e1, ← e2]
  · intro v hv
    unfold BranchingSupport.Rep.TK at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hx
      exact hsm g hg v₀ (hsmooth v₀ hv₀)
    | zero => exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_zero
    | add x y _ _ hx hy => exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_add hx hy
    | smul a x _ hx => exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_smul a hx
  · intro g hg v hv
    unfold BranchingSupport.Rep.TK at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, v₀, hv₀, rfl⟩ := hx
      refine Submodule.subset_span ⟨g * h, ?_, v₀, hv₀, (hmul g hg h hh v₀).symm⟩
      exact ofPI _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul (toPI g hg) (toPI h hh))
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · intro v hv
    unfold BranchingSupport.Rep.TK
    refine Submodule.subset_span ⟨1, ?_, v, hv, (hone v).symm⟩
    exact ofPI _ (by simp [PI.UpqRep.UH])
  · obtain ⟨w, hw1, hw⟩ := exists_isLowUnitH_of_isDSHpk hds
    exact ⟨w, hw1, PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw, hw⟩
  · intro v
    exact Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hds v

end GlobalTheory
