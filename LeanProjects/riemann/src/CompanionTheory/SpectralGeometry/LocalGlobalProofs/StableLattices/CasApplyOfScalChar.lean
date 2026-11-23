import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TraceElementsActByGelfandValues
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR

open scoped InnerProductSpace
open Formalism.REAL (GlRel IsUnitary KHighest Cas etr epow)

namespace GlobalTheory.CompanionTheory.RgExhUnit

theorem etr_two_eq_cas {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : etr E 2 = Cas E := by
  simp [etr, Cas, epow]

theorem cas_apply_of_scalChar {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (χ : Fin n → ℂ)
    (hS : CompanionTheory.RgExh.ScalChar ⟨V, E, hE⟩ χ) (u : V) :
    Cas E u = (∑ a, χ a * χ a -
      ∑ a, ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ) * ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ)) • u := by
  rcases n with _ | m
  · simp [Cas]
  · have h := GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli V m E χ u hE
      (fun Y => by
        have := LinearMap.congr_fun (hS Y) u
        simpa using this) 2
    rw [etr_two_eq_cas, GlobalTheory.CasimirEigen.gelfVal_two_eq] at h
    exact h

theorem re_sum_mul_self {n : ℕ} (χ : Fin n → ℂ) :
    (∑ a, χ a * χ a).re = ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Complex.mul_re, sq]

theorem unitIneq : CompanionTheory.RgExh.U.UnitIneq := by
  intro n
  refine ⟨∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a, ?_⟩
  intro ε V _ _ E hE χ γ u hU hS hu hK
  have h1 := Formalism.REAL.wdCas V n ε E γ u hE hU hK
  have hin : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [cas_apply_of_scalChar V E hE χ hS u, inner_smul_right, hin] at h1
  have h2 := congrArg Complex.re h1
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  have hsum : 0 ≤ ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) := by
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    split_ifs <;> positivity
  have hrho : (∑ a, ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ) * ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ)).re =
      ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.mul_re]
  have hc : (∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a) * ‖u‖ ^ 2 =
      (Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) - Formalism.REAL.nsq (Formalism.REAL.rhoC ε)) * ‖u‖ ^ 2 -
        ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) := by
    rw [Complex.re_mul_ofReal, Complex.ofReal_re, Complex.sub_re, re_sum_mul_self, hrho] at h2
    exact h2
  have hnn : 0 ≤ Formalism.REAL.nsq (Formalism.REAL.rhoC ε) := by
    show 0 ≤ ∑ a, Formalism.REAL.rhoC ε a * Formalism.REAL.rhoC ε a
    exact Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have hle : ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a ≤
      Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) - Formalism.REAL.nsq (Formalism.REAL.rhoC ε) := by
    refine le_of_mul_le_mul_right ?_ hpos
    rw [hc]
    linarith
  show _ ≤ Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) + _
  linarith

end GlobalTheory.CompanionTheory.RgExhUnit
