import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsBasic

noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def kG (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V') (γ : G) (q : G × G) :
    V' →L[ℂ] V :=
  ((d : ℂ) * ⟪σ q.1 w, σ γ (σ q.2 w)⟫_ℂ) • rk1A (W q.1) (W' q.2)

theorem rankOne_eq_smulRightL (a : V) (b : V') :
    rk1A a b = ContinuousLinearMap.smulRightL ℂ V' V (innerSL ℂ b) a := rfl

theorem norm_rk1A_le (a : V) (b : V') : ‖rk1A a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h : ‖rk1A a b‖ = ‖innerSL ℂ b‖ * ‖a‖ := ContinuousLinearMap.norm_smulRight_apply _ _
  rw [h, innerSL_apply_norm, mul_comm]

theorem continuous_rk1A {α : Type*} [TopologicalSpace α] {f : α → V} {g : α → V'} (hf : Continuous f)
    (hg : Continuous g) : Continuous (fun x => rk1A (f x) (g x)) := by
  simp only [rankOne_eq_smulRightL]
  exact ((ContinuousLinearMap.smulRightL ℂ V' V).continuous.comp
    ((innerSL ℂ).continuous.comp hg)).clm_apply hf

theorem continuous_kG {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (d : ℝ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) : Continuous (kG σ d w W W' γ) := by
  obtain ⟨-, -, -, hc⟩ := hσ
  have h1 : Continuous fun q : G × G => σ q.1 w := (hc w).comp continuous_fst
  have h2 : Continuous fun q : G × G => σ γ (σ q.2 w) :=
    (σ γ).continuous.comp ((hc w).comp continuous_snd)
  exact (continuous_const.mul (Continuous.inner (𝕜 := ℂ) h1 h2)).smul
    (continuous_rk1A (hW.comp continuous_fst) (hW'.comp continuous_snd))

theorem integral_kG {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {ν : Measure G} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (W' : G → V') (γ : G) (hi : Integrable (kG σ d w W W' γ) (μ.prod μ)) :
    ∫ q, kG σ d w W W' γ q ∂(μ.prod μ) = ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ := by
  obtain ⟨-, hmul, hunit, -⟩ := hσ
  obtain ⟨-, -, -, -, -, hrep, -⟩ := hW
  have hF : ∀ x : G, Integrable (fun g => ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g) μ ∧
      ∫ g, ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g ∂μ = W x := by
    intro x
    obtain ⟨hI, hE⟩ := hrep x
    have hin : ∀ g, ⟪σ g w, σ x w⟫_ℂ = conj ⟪w, σ (x⁻¹ * g) w⟫_ℂ := by
      intro g
      rw [inner_conj_symm, ← hunit x (σ (x⁻¹ * g) w) w, ← ContinuousLinearMap.mul_apply, ← hmul,
        mul_inv_cancel_left]
    have heq : (fun g => ((d : ℂ) * ⟪σ g w, σ x w⟫_ℂ) • W g)
        = fun g => (fun y => ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y)) (x⁻¹ * g) := by
      funext g
      simp only [mul_inv_cancel_left, hin]
    rw [heq]
    exact ⟨hI.comp_mul_left x⁻¹,
      (integral_mul_left_eq_self (fun y => ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y)) x⁻¹).trans hE⟩
  rw [integral_prod_symm _ hi]
  have hin : ∀ g' : G, ∫ g, kG σ d w W W' γ (g, g') ∂μ = rk1A (W (γ * g')) (W' g') := by
    intro g'
    have hk : (fun g => kG σ d w W W' γ (g, g'))
        = fun g => (ContinuousLinearMap.smulRightL ℂ V' V (innerSL ℂ (W' g')))
          (((d : ℂ) * ⟪σ g w, σ (γ * g') w⟫_ℂ) • W g) := by
      funext g
      simp only [kG, map_smul, ← rankOne_eq_smulRightL, hmul, ContinuousLinearMap.mul_apply]
    rw [hk, ContinuousLinearMap.integral_comp_comm _ (hF _).1, (hF _).2, ← rankOne_eq_smulRightL]
  simp_rw [hin]
  have h := integral_mul_left_eq_self (μ := μ) (fun x => rk1A (W x) (W' (γ⁻¹ * x))) γ
  simp only [inv_mul_cancel_left] at h
  exact h

end Formalism.L2.S.Pv.EnergyAbs
