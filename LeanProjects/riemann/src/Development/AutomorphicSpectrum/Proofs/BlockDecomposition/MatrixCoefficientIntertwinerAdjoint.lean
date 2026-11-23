import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TwPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem inner_map_map (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨_, _, hnorm, _⟩ := hU
  let L : A →ₗᵢ[ℂ] A := ⟨(ρ g : A →ₗ[ℂ] A), hnorm g⟩
  exact L.inner_map_map x y

theorem map_mul_apply (hU : IsU ρ) (g h : Γ) (x : A) : ρ (g * h) x = ρ g (ρ h x) := by
  obtain ⟨_, hmul, _, _⟩ := hU
  rw [hmul, ContinuousLinearMap.mul_apply]

theorem inner_translate (hU : IsU ρ) (a g b : Γ) (u : A) :
    ⟪ρ a u, ρ g (ρ b u)⟫_ℂ = ⟪u, ρ (a⁻¹ * g * b) u⟫_ℂ := by
  have h : ρ g (ρ b u) = ρ a (ρ (a⁻¹ * g * b) u) := by
    rw [← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, ← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, show a * (a⁻¹ * g * b) = g * b by group]
  rw [h, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_map_map hU]

end Unitary

theorem coefOp_translate {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ) (hρ : IsU ρ) (w₀ : A) (v : B)
    (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) (x y : Γ) :
    ⟪σ x w₀, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm (σ y w₀)⟫_ℂ =
      star ⟪ρ x⁻¹ v, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc (ρ y⁻¹ v)⟫_ℂ := by
  rw [GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp]
  simp_rw [GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hσ, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hρ, inv_inv]
  have key : ∀ F : Γ → ℂ, ∫ g, F (x⁻¹ * g * y) ∂ν = ∫ g, F g ∂ν := fun F =>
    (integral_mul_left_eq_self (fun h => F (h * y)) x⁻¹).trans (integral_mul_right_eq_self F y)
  have hstar : star (∫ g, star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν) =
      ∫ g, ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν := by
    have h := (integral_conj (μ := ν)
      (f := fun g => star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)).symm
    simpa [map_mul] using h
  rw [hstar, ← key (fun g => ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [show x * (x⁻¹ * g * y) * y⁻¹ = g by group]
  exact mul_comm _ _

end GlobalTheory.CompanionTheory.RgHeA.TwPf
