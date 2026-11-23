import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible

noncomputable section

namespace GlobalTheory.UnitK

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem vEqK_zero_of_norm_one : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (x : X.G.Kf), ‖E.iK x‖ = 1 → X.vEqK x 0 := by
  intro p _ X hfr E x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨N, hN⟩ := Formalism.MainNotions.FormalGroupSystem.Pf.exists_rep X hfr hx0

  have hint : ∀ y : X.G.Kf, ‖E.iK y‖ = 1 → y ∈ X.intK := fun y hy =>
    (E.mem_iff y).1 (by rw [mem_OcC]; exact hy.le)
  have h1 : X.vGeK x 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x hx)
  have h2 : X.vGeK x⁻¹ 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x⁻¹ (by rw [map_inv₀, norm_inv, hx, inv_one]))
  have hN1 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr hN 0).1 h1
  have hN2 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr (Formalism.MainNotions.FormalGroupSystem.Pf.Rep.inv X hN) 0).1 h2
  simp only [zero_mul] at hN1 hN2
  have hN0 : N = 0 := by
    have a : (0 : ℤ) ≤ N := by exact_mod_cast hN1
    have b : (0 : ℤ) ≤ -N := by exact_mod_cast hN2
    omega

  have he : 0 < X.eO := by
    rcases Nat.eq_zero_or_pos X.eO with h0 | h0
    · exfalso
      obtain ⟨u, hu⟩ := X.eO_spec
      rw [h0, pow_zero] at hu

      have hpu : IsUnit (p : X.G.O) := by
        exact IsUnit.of_mul_eq_one _ hu
      obtain ⟨w, hw⟩ := hpu.exists_right_inv
      have hb := E.int w
      have hmul : E.iK (algebraMap X.G.O X.G.Kf (p : X.G.O)) * E.iK (algebraMap X.G.O X.G.Kf w) = 1 := by
        rw [← map_mul, ← map_mul, hw, map_one, map_one]
      have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
        have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
        rw [this, norm_algebraMap', Padic.norm_p]
      rw [map_natCast, map_natCast] at hmul
      have hn2 := congrArg norm hmul
      rw [norm_mul, norm_one, hn] at hn2
      have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      have hp0 : (0 : ℝ) < p := by linarith
      have : ‖E.iK (algebraMap X.G.O X.G.Kf w)‖ = p := by
        field_simp at hn2
        linarith
      linarith
    · exact h0
  exact (Formalism.MainNotions.FormalGroupSystem.Pf.vEqK_iff_of_rep X hfr hN 0).2 ⟨he, by simp [hN0]⟩

end GlobalTheory.UnitK
