import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfIsTypeOfParamEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_comp_isometryEquiv {V₁ V₂ V₃ : Type} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [CompleteSpace V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [CompleteSpace V₂]
    [NormedAddCommGroup V₃] [InnerProductSpace ℂ V₃] [CompleteSpace V₃]
    (A : V₂ →L[ℂ] V₁) (φ : V₃ ≃ₗᵢ[ℂ] V₂) (v : V₁) :
    ‖ContinuousLinearMap.adjoint (A.comp (φ : V₃ →L[ℂ] V₂)) v‖ = ‖ContinuousLinearMap.adjoint A v‖ := by
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]
  simp

theorem exists_wigMap_pair_of_isType : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (u up um : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → IsType k r z πp up → IsType k r z πm um → (∀ i ∈ Finset.Icc 1 k, up i = if i = l + 1 then u i + (n₀ : ℝ) else u i) → (∀ i ∈ Finset.Icc 1 k, um i = if i = l then u i - (n₀ : ℝ) else u i) → ∃ (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ k r z π πp πm u up um l n₀ b hz hT hπ hgap hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Vp', _, _, _, Vm', _, _, _, πp', πm', Ap', Am', hp', hm', hAp, hAm, hlb⟩ :=
    GlobalTheory.T.exists_shifted_types_lower_bound_alt V k r z π u l n₀ b hz hT hπ hgap hl hlk hn hb hnb h1b
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨φp, hφp⟩ := GlobalTheory.exists_isometry_of_isType_of_param_eq Vp Vp' n r z πp πp' _ _ hz hT hp hp' (by
    intro i hi
    rw [hup i hi, Function.update_apply]
    split_ifs with h
    · rw [h]
    · rfl)
  obtain ⟨φm, hφm⟩ := GlobalTheory.exists_isometry_of_isType_of_param_eq Vm Vm' n r z πm πm' _ _ hz hT hm hm' (by
    intro i hi
    rw [hum i hi, Function.update_apply]
    split_ifs with h
    · rw [h]
    · rfl)
  refine ⟨fun ω => (Ap' ω).comp (φp : Vp →L[ℂ] Vp'), fun ω => (Am' ω).comp (φm : Vm →L[ℂ] Vm'), ?_, ?_, ?_⟩
  · exact wigMap_comp V Vp' Vp (n + 1) r z π πp' πp n₀ 0 Ap' (fun _ => (φp : Vp →L[ℂ] Vp')) hAp
      (wigMap_zero_of_contraction Vp' Vp (n + 1) r z πp' πp _ (fun v => by simp)
        (fun h hh v => by simpa using hφp h hh v))
  · exact wigMap_comp V Vm' Vm (n + 1) r z π πm' πm n₀ 0 Am' (fun _ => (φm : Vm →L[ℂ] Vm')) hAm
      (wigMap_zero_of_contraction Vm' Vm (n + 1) r z πm' πm _ (fun v => by simp)
        (fun h hh v => by simpa using hφm h hh v))
  · intro ω hω hωz v
    rw [norm_adjoint_comp_isometryEquiv, norm_adjoint_comp_isometryEquiv]
    exact hlb ω hω hωz v

end GlobalTheory.WigSh
