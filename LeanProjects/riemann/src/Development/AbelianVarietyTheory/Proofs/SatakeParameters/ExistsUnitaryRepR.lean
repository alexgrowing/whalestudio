import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection

open MeasureTheory

noncomputable section

namespace GlobalTheory.AutomorphicL2Unitary

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def Riso (g : G) : L2 Γ μ ≃ₗᵢ[ℂ] L2 Γ μ where
  toLinearEquiv := LinearEquiv.ofLinear (R Γ μ g).toLinearMap (R Γ μ g⁻¹).toLinearMap
    (by ext F; simp [← ContinuousLinearMap.mul_apply, ← map_mul])
    (by ext F; simp [← ContinuousLinearMap.mul_apply, ← map_mul])
  norm_map' := norm_R g

@[simp] theorem Riso_apply (g : G) (F : L2 Γ μ) : Riso Γ μ g F = R Γ μ g F := rfl

def Rhom : G →* (L2 Γ μ ≃ₗᵢ[ℂ] L2 Γ μ) where
  toFun := Riso Γ μ
  map_one' := LinearIsometryEquiv.ext fun F => by simp
  map_mul' g h := LinearIsometryEquiv.ext fun F => by
    show R Γ μ (g * h) F = R Γ μ g (R Γ μ h F)
    rw [map_mul]; rfl

def Rurep : GroundTheory.Automorphic.UnitaryRep G (L2 Γ μ) :=
  GroundTheory.Automorphic.UnitaryRep.ofLinearIsometryEquiv (Rhom Γ μ) fun F => continuous_R F

end GlobalTheory.AutomorphicL2Unitary
