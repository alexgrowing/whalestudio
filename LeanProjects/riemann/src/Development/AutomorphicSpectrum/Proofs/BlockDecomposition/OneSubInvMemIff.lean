import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.KirTorus

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem val_eq_one {x : F} {n : ℕ} (hn : 1 ≤ n) (hx : x - 1 ∈ valBall F (n : ℤ)) :
    normalizedValuation F x = 1 := by
  have h1 : normalizedValuation F (x - 1) < 1 := by
    refine lt_of_le_of_lt (mem_valBall.mp hx) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    have : (1 : ℤ) ≤ n := by exact_mod_cast hn
    omega
  have := Valuation.map_one_add_of_lt (normalizedValuation F) h1
  simpa using this

theorem inv_sub_one_mem {x : F} {n : ℕ} (hn : 1 ≤ n) (hx0 : x ≠ 0)
    (hx : x - 1 ∈ valBall F (n : ℤ)) : x⁻¹ - 1 ∈ valBall F (n : ℤ) := by
  have hv := val_eq_one hn hx
  have e : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by field_simp; ring
  rw [e, mem_valBall, map_mul, Valuation.map_neg, map_inv₀, hv, inv_one, mul_one]
  exact mem_valBall.mp hx

theorem mul_sub_one_mem {x y : F} {n : ℕ} (hn : 1 ≤ n) (hx : x - 1 ∈ valBall F (n : ℤ))
    (hy : y - 1 ∈ valBall F (n : ℤ)) : x * y - 1 ∈ valBall F (n : ℤ) := by
  have hv := val_eq_one hn hy
  have e : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [e]
  refine add_mem ?_ hy
  rw [mem_valBall, map_mul, hv, mul_one]
  exact mem_valBall.mp hx

variable [MeasurableSpace F] [BorelSpace F]

theorem localFourier_torG {ψ : AddChar F Circle} (hψ : IsStd ψ) (n : ℕ) (y : F) :
    localFourier (selfDualMeasure ψ) ψ (torG ψ n) y =
      (((selfDualMeasure ψ).real (valBall F (-(n : ℤ)) : Set F) : ℝ) : ℂ) *
        (valBall F (n : ℤ) : Set F).indicator (fun _ => (1 : ℂ)) (1 + y) := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have key := localFourier_indicator_valBall (selfDualMeasure ψ) hc h1 (-(n : ℤ)) (1 + y)
  rw [h0, zero_sub, neg_neg] at key
  rw [← key]
  unfold localFourier
  congr 1
  funext x
  by_cases hx : x ∈ (valBall F (-(n : ℤ)) : Set F)
  · rw [torG, Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_add, mul_one,
      AddChar.map_add_eq_mul, Circle.coe_mul, one_mul]
  · rw [torG, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, zero_mul]

theorem one_sub_inv_mem_iff {n : ℕ} (hn : 1 ≤ n) (h : Fˣ) :
    (1 + -((h⁻¹ : Fˣ) : F)) ∈ valBall F (n : ℤ) ↔ (h : F) - 1 ∈ valBall F (n : ℤ) := by
  constructor
  · intro hh
    have h2 : ((h⁻¹ : Fˣ) : F) - 1 ∈ valBall F (n : ℤ) := by
      have := neg_mem hh
      rwa [show -(1 + -((h⁻¹ : Fˣ) : F)) = ((h⁻¹ : Fˣ) : F) - 1 by ring] at this
    have := inv_sub_one_mem hn (h⁻¹).ne_zero h2
    simpa using this
  · intro hh
    have h2 := inv_sub_one_mem hn h.ne_zero hh
    have := neg_mem h2
    rw [show -((h : F)⁻¹ - 1) = 1 + -((h⁻¹ : Fˣ) : F) by simp; ring] at this
    exact this

theorem torus_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (n : ℕ), 1 ≤ n → (∀ a : Fˣ, (a : F) - 1 ∈ valBall F (n : ℤ) → ν a = 1) →
  ∀ a : Fˣ,
    ((a : F) - 1 ∈ valBall F (n : ℤ) → ∫ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * torF F n ((h : F) * a) *
        localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) ∂multHaar F =
      (((selfDualMeasure ψ).real (valBall F (-(n : ℤ)) : Set F) : ℝ) : ℂ) * (((multHaar F).real {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} : ℝ) : ℂ)) ∧
    ((a : F) - 1 ∉ valBall F (n : ℤ) → ∫ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * torF F n ((h : F) * a) *
        localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) ∂multHaar F = 0) := by
  intro F _ _ _ _ _ _ ψ hψ ν n hn hν a
  set V : ℂ := (((selfDualMeasure ψ).real (valBall F (-(n : ℤ)) : Set F) : ℝ) : ℂ) with hV
  set H : Set Fˣ := {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} with hH
  have hfour : ∀ h : Fˣ, localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) =
      H.indicator (fun _ => V) h := by
    intro h
    rw [localFourier_torG hψ]
    by_cases hh : h ∈ H
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem
        (show (1 + -((h⁻¹ : Fˣ) : F)) ∈ (valBall F (n : ℤ) : Set F) from
          (one_sub_inv_mem_iff hn h).mpr hh), mul_one]
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem
        (show (1 + -((h⁻¹ : Fˣ) : F)) ∉ (valBall F (n : ℤ) : Set F) from
          fun h' => hh ((one_sub_inv_mem_iff hn h).mp h')), mul_zero]
  have hmeas : MeasurableSet H :=
    ((isOpen_valBall (n : ℤ)).preimage
      ((Units.continuous_val).sub continuous_const)).measurableSet
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · have e : ∀ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * torF F n ((h : F) * a) *
        localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) =
        H.indicator (fun _ => V) h := by
      intro h
      rw [hfour]
      by_cases hh : h ∈ H
      · have hνh : ν h = 1 := hν h hh
        have hm : (h : F) * a ∈ {x : F | x - 1 ∈ valBall F (n : ℤ)} := mul_sub_one_mem hn hh ha
        rw [Set.indicator_of_mem hh, torF, Set.indicator_of_mem hm, MonoidHom.inv_apply, hνh]
        simp
      · rw [Set.indicator_of_notMem hh, mul_zero]
    simp_rw [e]
    rw [integral_indicator_const _ hmeas, Complex.real_smul, mul_comm]
  · have e : ∀ h : Fˣ, (((ν h)⁻¹ * ν⁻¹ h : ℂˣ) : ℂ) * torF F n ((h : F) * a) *
        localFourier (selfDualMeasure ψ) ψ (torG ψ n) (-((h⁻¹ : Fˣ) : F)) = 0 := by
      intro h
      rw [hfour]
      by_cases hh : h ∈ H
      · have hm : (h : F) * a ∉ {x : F | x - 1 ∈ valBall F (n : ℤ)} := by
          intro hm
          apply ha
          have h2 := inv_sub_one_mem hn h.ne_zero hh
          have := mul_sub_one_mem hn h2 hm
          rwa [inv_mul_cancel_left₀ h.ne_zero] at this
        rw [torF, Set.indicator_of_notMem hm, mul_zero, zero_mul]
      · rw [Set.indicator_of_notMem hh, mul_zero]
    simp_rw [e]
    simp

end GlobalTheory.CompanionTheory.KirTorus
