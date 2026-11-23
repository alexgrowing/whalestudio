import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAvgForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepTrilinearFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepLocalWeilActionLineCharactersCancelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DblInv

theorem val_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ)
    (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Θ₁ : WO S.B.V S.J.W → ℂ) (Θ₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ)
    (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    S.val c₁ c₂ Θ₁ Θ₂ φ f g h₁ h₂ = S.val c₁ c₂ (S.s₁.om (g, h₁) Θ₁) (S.s₂.om (h₁, h₂) Θ₂) φ (rTrans h₂ f) 1 1 1 := by
  unfold Dbl2.val Dbl2.con
  have e3 : rTrans (1 : GA D S.B'.V) (rTrans h₂ f) = rTrans h₂ f := by funext x; simp [rTrans]
  rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
    map_one, map_one, e3]
  rfl

set_option maxHeartbeats 2000000 in

theorem val_inv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → Q.Typed f → ∀ g h₁ h₂, g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v) → h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v) → h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v) → ∀ a x y, ∀ r ∈ RFJ Q.k Q.n₁ (Q.c + 1 + 1) (σ + 1), ∀ j ∈ Q.L₁.J, ∀ r' ∈ R Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ j' ∈ Q.L₂.J, S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ (r * x * j)) (h₂ * Q.gl₂ (r' * y * j')) = S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ f₁ f₂ hvac φ f hφ hf hTy g h₁ h₂ hg hh₁ hh₂ a x y r hr j hj r' hr' j' hj'
  obtain ⟨⟨T₁, O₁, hT₁, hO₁, rfl⟩, ⟨T₂, O₂, hT₂, hO₂, rfl⟩⟩ := hvac
  have hcQ : Q.c + 1 + 1 = 2 * (σ + 1) := by have := Q.F.bes.1; omega
  obtain ⟨hψc, hψ1⟩ := GlobalTheory.T.addChar_conductor_integers_continuous_ne_one Q.k Q.ψk Q.cond
  have hsd : IsSelfDual Q.ψk Q.ν := ((GlobalTheory.SplitWeil.selfDual_measure Q.k Q.ψk hψc hψ1).2.1 Q.cond Q.ν).1 Q.unitVol
  obtain ⟨-, -, -, cm₀, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B.V _ Q.F.G₀ Q.gl₀ Q.loc₀
  obtain ⟨-, -, -, cm₁, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.J.W _ Q.F.G₁ Q.gl₁ Q.loc₁
  obtain ⟨-, -, -, cm₂, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂
  have hT₁' := GlobalTheory.T.local_model_weil_operator_trivialAtPlace_isModel D Q.k Q.q ψ hψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil _ _ Q.F.G₀ Q.F.G₁ T₁ hT₁ g hg h₁ hh₁
  have hT₂' := GlobalTheory.T.local_model_weil_operator_trivialAtPlace_isModel D Q.k Q.q ψ hψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil _ _ Q.F.G₁ Q.F.G₂ T₂ hT₂ h₁ hh₁ h₂ hh₂
  have hf' : IsContAut S.B'.V (rTrans h₂ f) :=
    ⟨fun γ hγ x => by simp only [rTrans, mul_assoc]; exact hf.1 γ hγ _, hf.2.comp (continuous_mul_right h₂)⟩
  have hTy' : Q.Typed (rTrans h₂ f) := fun j => by
    funext x
    have := congrFun (hTy j) (x * h₂)
    simp only [rTrans, Pi.smul_apply] at this ⊢
    rw [mul_assoc, cm₂ j h₂ hh₂, ← mul_assoc, this]
  obtain ⟨A, τ, T, hsm, hτ, hmem, htri, hval, -⟩ :=
    GlobalTheory.T.splitPlace_doubleStep_trilinearForm_properties D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ _ _ hT₁' hT₂' φ hφ
  set F : A := ⟨rTrans h₂ f, hmem _ hf' hTy'⟩ with hFdef
  let Φa : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k →
      SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
    fun x => ⟨om Q.μ₁ a x Q.Φ₁.1, om_mem_SB Q.μ₁ a x Q.Φ₁.2⟩
  let Φb : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k →
      SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x y => ⟨om Q.μ₂ x y Q.Φ₂.1, om_mem_SB Q.μ₂ x y Q.Φ₂.2⟩
  have d1 : comb ψ _ _ Q.D₁ (T₁ O₁) = T₁ Q.Φ₁ := (Q.dat₁.2 T₁ hT₁ O₁ Q.Φ₁ hO₁ rfl).symm
  have d2 : comb ψ _ _ Q.D₂ (T₂ O₂) = T₂ Q.Φ₂ := (Q.dat₂.2 T₂ hT₂ O₂ Q.Φ₂ hO₂ rfl).symm
  have KEY : ∀ x y, S.val c₁ c₂ (comb ψ _ _ Q.D₁ (T₁ O₁)) (comb ψ _ _ Q.D₂ (T₂ O₂)) φ f (g * Q.gl₀ a)
      (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) =
      S.val c₁ c₂ ((S.s₁.om (g, h₁) ∘ₗ T₁) (Φa x)) ((S.s₂.om (h₁, h₂) ∘ₗ T₂) (Φb x y)) φ (τ y F).1 1 1 1 := by
    intro x y
    rw [d1, d2, val_move]
    have m1 : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (Q.gl₀ a, Q.gl₁ x) * S.s₁.om (g, h₁) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₀ a g hg, cm₁ x h₁ hh₁]
    have m2 : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (Q.gl₁ x, Q.gl₂ y) * S.s₂.om (h₁, h₂) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₁ x h₁ hh₁, cm₂ y h₂ hh₂]
    have r : rTrans (h₂ * Q.gl₂ y) f = (τ y F).1 := by
      rw [hτ]; funext z; simp only [rTrans, hFdef]; rw [mul_assoc z (Q.gl₂ y) h₂, cm₂ y h₂ hh₂]
    rw [m1, m2, r, Module.End.mul_apply, Module.End.mul_apply]
    exact GlobalTheory.T.doubleStep_local_weil_action_line_characters_cancel D ψ hψ σ S Q _ _ hT₁' hT₂' c₁ c₂ φ _ a x y Q.Φ₁ (Φa x) Q.Φ₂ (Φb x y) rfl rfl
  have hFty : ∀ j : Q.L₂.J, τ (j : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) F = (Q.L₂.lam j : ℂ) • F := by
    intro j; apply Subtype.ext; rw [hτ, Submodule.coe_smul]; exact hTy' j
  rw [KEY, KEY]
  exact tensorVal_inv hcQ hψc hψ1 hsd Q.open₂ htri F Q.Φ₁ Q.Φ₂ Q.ty₁ Q.ty₂ hFty a x y hr hj hr' hj'
    (hval (Φa _) (Φb _ _) (τ _ F)) (hval (Φa x) (Φb x y) (τ y F))

end GlobalTheory.DblInv
end
