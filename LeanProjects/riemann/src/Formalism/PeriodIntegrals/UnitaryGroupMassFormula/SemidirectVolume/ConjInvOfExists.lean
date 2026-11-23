import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SubgroupLocallyCompactHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.DiscAll

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def ModOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ h ∈ Hsub (AF F) σ J P, ∃ μ : Measure (FrameUnipotentSubgroup (AF F) σ J P), μ.IsHaarMeasure ∧
      ∀ f : HA (AF F) σ J → ENNReal, Measurable f →
        ∫⁻ n, f (h * (n : HA (AF F) σ J) * h⁻¹) ∂μ = ∫⁻ n, f (n : HA (AF F) σ J) ∂μ

theorem conjInv_of_exists {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by
  obtain ⟨hlc, hsc, ht2, htg⟩ := hN
  intro μN hμN h hh f hf
  obtain ⟨μ0, hμ0, hinv⟩ := hex h hh
  rw [Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure,
    hinv f hf]

theorem conjStep_of (hM : ModOne) : ConjStep := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T hr hP
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  have hX := Lc.locally_compact_adelic_unitary F E σ hCM M J hJ
  obtain ⟨-, cN, -⟩ := closed_subgroup_holds F E σ hCM M J hJ r P T hr hP
  obtain ⟨hcnt, hdisc⟩ := discrete_adelic_unitary F E σ hCM M J hJ
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cN
    hcnt hdisc
  exact conjInv_of_exists _ _ lN (hM F E σ hCM M J hJ r P T hr hP)

end PI.VolSemiDirect.W.Cj
