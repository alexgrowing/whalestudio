import Mathlib
import Formalism.PeriodIntegrals.PhConvProj

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhConvProj.Defs

open PI.PhConvProj

def SelfAdjStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → ∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ

def SandStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → ∀ a, T.comp ((π a).comp T) = m a • T

theorem convProj_of (h1 : SelfAdjStep) (h2 : SandStep) : ConvProj := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m hph hci K _ _ π T hπ hT
  have hsa := h1 G μ ph m hph hci K π T hπ hT
  have hsw := h2 G μ ph m hph hci K π T hπ hT
  obtain ⟨hπ1, -⟩ := hπ
  obtain ⟨hm1, -⟩ := hci
  refine ⟨hsa, ?_, hsw⟩
  have h := hsw 1
  rw [hπ1, hm1, one_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] at h
  exact h

end PI.UnitaryGroupMassFormula.PhConvProj.Defs
