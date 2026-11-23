import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInst

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tauU {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) : X.Vpi u →L[ℂ] X.Vpi u :=
  X.psiInfU u s • X.piU u s

def StepSchurG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    IsUnitRep X.B.σs ∧ IsSchur (Formalism.L2.SG.ProjRows.muInf X.B.I) X.B.σs (degX X) ∧ ‖X.B.tens X.B.w‖ = 1 ∧
      ∀ y : X.B.I.Ginf, (Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv y) =
        ((degX X : ℝ) : ℂ) * conj ⟪X.B.tens X.B.w, X.B.σs y (X.B.tens X.B.w)⟫_ℂ

def StepSubG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarSub (X.SinfU u) (muS X u) ∧ IsFolner (X.SinfU u) (muS X u) ∧
      tauU X u 1 = 1 ∧ (∀ s ∈ X.SinfU u, ∀ t ∈ X.SinfU u, tauU X u (s * t) = tauU X u s * tauU X u t) ∧
      SFinite (X.nuQ u)

def StepSection : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∃ h : Cinf X → X.B.I.Ginf, Measurable h ∧ ∀ c ∈ Good X u u', HasDiag X u u' sc c (h c)

def StepConv : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    (∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
          X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
        ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤) ∧
    ∀ w : D.what₂.Word,
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
        ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem tauU_unit (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) (a b : X.Vpi u) :
    ⟪tauU X u s a, tauU X u s b⟫_ℂ = ⟪a, b⟫_ℂ := by
  simp only [tauU, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, (X.piU_rep u).2.2.1 s hs]
  rw [← mul_assoc, Complex.mul_conj', Formalism.L2.SG.RealObj.InfCut.norm_psiInfU]
  simp

theorem isWAbs_of (hS : StepSchurG) (hG : StepSubG) (u : D.what₂.Word) :
    IsWAbs (Formalism.L2.SG.ProjRows.muInf X.B.I) X.B.σs (degX X) (X.B.tens X.B.w) (X.SinfU u) (tauU X u)
      (X.nuQ u) (X.Wu u) := by
  obtain ⟨-, -, -, hph⟩ := hS D X
  obtain ⟨-, -, h1, hmul, -⟩ := hG D X u
  have hW := X.Wu_spec u
  refine ⟨h1, hmul, fun s hs a b => tauU_unit X u s hs a b, fun s hs x => ?_, hW.2.2.1, fun x => ?_,
    hW.2.2.2.1, hW.2.2.2.2⟩
  · rw [hW.1 s hs x]; rfl
  · obtain ⟨hi, he⟩ := hW.2.1 x
    have e : (fun y => (((degX X : ℝ) : ℂ) * conj ⟪X.B.tens X.B.w, X.B.σs y (X.B.tens X.B.w)⟫_ℂ) • X.Wu u (x * y)) =
        fun y => Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv y • X.Wu u (x * y) :=
      funext fun y => by rw [hph y]
    rw [e]
    exact ⟨hi, he⟩

theorem inner_transfer (hG : StepSubG) (u u' : D.what₂.Word) (φ : X.B.I.Ginf → ℝ≥0∞) (hφ : Measurable φ)
    (γ γ' : X.B.I.Ginf) (a : X.B.I.Ginf) (ha : a ∈ X.SinfU u) (b : X.B.I.Ginf) (hb : b ∈ X.SinfU u')
    (hγ : γ' = a * γ * b⁻¹) :
    ∫⁻ s, ∫⁻ s', φ (s * γ' * s'⁻¹) ∂(muS X u') ∂(muS X u) = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂(muS X u') ∂(muS X u) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hR, -⟩ := (hG D X u).1
  obtain ⟨-, -, -, -, -, -, -, -, -, hR', -⟩ := (hG D X u').1
  subst hγ
  have hin : ∀ s, ∫⁻ s', φ (s * (a * γ * b⁻¹) * s'⁻¹) ∂(muS X u') = ∫⁻ s', φ (s * a * γ * s'⁻¹) ∂(muS X u') := by
    intro s
    have e : ∀ s', s * (a * γ * b⁻¹) * s'⁻¹ = s * a * γ * (MeasurableEquiv.mulRight b s')⁻¹ := by
      intro s'
      simp only [MeasurableEquiv.coe_mulRight]
      group
    simp_rw [e]
    rw [← lintegral_map_equiv (fun t => φ (s * a * γ * t⁻¹)) (MeasurableEquiv.mulRight b),
      MeasurableEquiv.coe_mulRight, hR' b hb]
  simp_rw [hin]
  have e2 : ∀ s, (∫⁻ s', φ (s * a * γ * s'⁻¹) ∂(muS X u')) =
      (fun t => ∫⁻ s', φ (t * γ * s'⁻¹) ∂(muS X u')) (MeasurableEquiv.mulRight a s) := by
    intro s
    simp only [MeasurableEquiv.coe_mulRight]
  simp_rw [e2]
  rw [← lintegral_map_equiv (fun t => ∫⁻ s', φ (t * γ * s'⁻¹) ∂(muS X u')) (MeasurableEquiv.mulRight a),
    MeasurableEquiv.coe_mulRight, hR a ha]

end Formalism.L2.SG.RealObj.EnergyInst
