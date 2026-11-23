import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay Formalism.L2.SG.WuDecayPf
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

def CoefDec (a : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ v (g : Formalism.REAL.UJ (X.B.I.ε v)), ‖coefV X v g‖ ≤ K * opn (uMat g) ^ (-a)

def MDec (a : ℝ) : Prop :=
  ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ g : X.B.I.Ginf, ‖mX X g‖ₑ ≤ K * ENNReal.ofReal (normInf X g ^ (-a))

def GrowthG (A : ℝ) : Prop :=
  ∫⁻ x, ENNReal.ofReal (normInf X x ^ (-A)) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤

def GrowthS (u : D.what₂.Word) (B : ℝ) : Prop :=
  ∫⁻ s, ENNReal.ofReal (normInf X s ^ (-B)) ∂(muS X u) < ⊤

def PropP (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (M : ℝ) : Prop :=
  ∃ CP : ℝ, 1 ≤ CP ∧ ∀ s ∈ X.SinfU u, ∀ s' ∈ X.SinfU u',
    max (normInf X s) (normInf X s') ≤ CP * normInf X (s * γ * s'⁻¹) ^ M

def LaFin (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (b : ℝ) : Prop :=
  ∫⁻ s, ∫⁻ s', ENNReal.ofReal (normInf X (s * γ * s'⁻¹) ^ (-b)) ∂(muS X u') ∂(muS X u) < ⊤

def NormInv : Prop := ∀ g : X.B.I.Ginf, normInf X g⁻¹ = normInf X g

def RealInputs : Prop :=
  ∃ a b M : ℝ, 0 ≤ b ∧ b ≤ a ∧ 0 < M ∧ CoefDec X a ∧ GrowthG X (a - b) ∧
    (∀ u, GrowthS X u (b / (2 * M))) ∧
    ∀ (u u' : D.what₂.Word) (sc : ℝ), ∀ c ∈ Formalism.L2.SG.RealObj.Good X u u', ∀ γ,
      Formalism.L2.SG.RealObj.HasDiag X u u' sc c γ → PropP X u u' γ M

end Defs

def StIntOfLint : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf),
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ →
      Formalism.L2.SG.TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

def StMDec : Prop := ∀ (D : D7) (X : HidaSetting D) (a : ℝ), CoefDec X a → MDec X a

def StLa : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (M b : ℝ), 0 < M → 0 ≤ b →
    (∀ g, 1 ≤ normInf X g) → PropP X u u' γ M → GrowthS X u (b / (2 * M)) → GrowthS X u' (b / (2 * M)) →
      LaFin X u u' γ b

def StTheta : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (a b : ℝ),
    (∀ g, 1 ≤ normInf X g) → NormInv X → 0 ≤ b → b ≤ a → WuDom X u → WuDom X u' → MDec X a →
      GrowthG X (a - b) → LaFin X u u' γ b →
        ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤

def StNormOne : Prop := ∀ (D : D7) (X : HidaSetting D), 0 < X.B.I.n → ∀ g, 1 ≤ normInf X g

def StNormInv : Prop := ∀ (D : D7) (X : HidaSetting D), NormInv X

end Formalism.L2.SG.RealObj.StepIntOf

namespace Formalism.L2.SG.RealObj.StepIntOf.Steps

open Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_rank_one_le {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (v : V) (w : V') :
    ‖Formalism.L2.SG.TermOp.rk1 v w‖ ≤ ‖v‖ * ‖w‖ := by
  unfold Formalism.L2.SG.TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem stIntOfLint : StIntOfLint := by
  intro D X u u' γ hfin
  unfold Formalism.L2.SG.TermOp.OOInt
  rw [integrableOn_univ]
  have hW : Continuous (X.Wu u) := (X.Wu_spec u).2.2.1
  have hW' : Continuous (X.Wu u') := (X.Wu_spec u').2.2.1
  have hW'' : Continuous fun x : X.B.I.Ginf => X.Wu u' (γ⁻¹ * x) := hW'.comp (continuous_const.mul continuous_id)
  have hc : Continuous fun x : X.B.I.Ginf => Formalism.L2.SG.TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) := by
    rw [continuous_clm_apply]
    intro ξ
    simp only [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply]
    exact (hW''.inner continuous_const).smul hW
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  simp only []
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_rank_one_le _ _)

end Formalism.L2.SG.RealObj.StepIntOf.Steps

namespace Formalism.L2.SG.RealObj.StepIntOf.Theta

open Formalism.L2.SG.RealObj.StepIntOf

section

variable {D : D7} (X : HidaSetting D)

end

end Formalism.L2.SG.RealObj.StepIntOf.Theta

namespace Formalism.L2.SG.RealObj.StepIntOf

end Formalism.L2.SG.RealObj.StepIntOf
