import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepTrilinearFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionsDoubleIntegralExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepLocalWeilActionLineCharactersCancelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLinearModelGLPairApplyMemSchwartzBruhatFuStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralsPositionOneEqCellSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ValOneAt

theorem val_translate {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ)
    (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Θ₁ : WO S.B.V S.J.W → ℂ) (Θ₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ)
    (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    S.val c₁ c₂ Θ₁ Θ₂ φ f g h₁ h₂ = S.val c₁ c₂ (S.s₁.om (g, h₁) Θ₁) (S.s₂.om (h₁, h₂) Θ₂) φ (rTrans h₂ f) 1 1 1 := by
  unfold Dbl2.val Dbl2.con
  have e3 : rTrans (1 : GA D S.B'.V) (rTrans h₂ f) = rTrans h₂ f := by funext x; simp [rTrans]
  rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
    map_one, map_one, e3]
  rfl

theorem sum_rTrans_trc {D : D7} {V : HSp D} {G : Type} [Monoid G] (gl : G →* GA D V) (h₂ : GA D V)
    (cm : ∀ b, gl b * h₂ = h₂ * gl b) (e : G →₀ ℂ) (f : GA D V → ℂ) :
    (e.sum fun b a => a • rTrans (gl b) (rTrans h₂ f)) = rTrans h₂ (trc (e.mapDomain gl) f) := by
  have e1 : trc (e.mapDomain gl) f = (e.mapDomain gl).sum fun b a => a • rTrans b f := rfl
  rw [e1, Finsupp.sum_mapDomain_index (h := fun b a => a • rTrans b f) (fun _ => zero_smul ℂ _)
    (fun _ _ _ => add_smul _ _ _)]
  funext w
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rTrans, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, cm b, ← mul_assoc]

theorem comb_lin {G A : Type} [AddCommGroup A] [Module ℂ A] [Monoid G] (τ : Representation ℂ G A) (l : A →ₗ[ℂ] ℂ)
    (e : G →₀ ℂ) (F : A) : GlobalTheory.PosOne.comb e (fun b => l (τ b F)) = l (e.sum fun b a => a • τ b F) := by
  simp only [GlobalTheory.PosOne.comb, Finsupp.sum, map_sum, map_smul, smul_eq_mul]

theorem coe_sum_sub {G X : Type} [AddCommGroup X] [Module ℂ X] {A : Submodule ℂ X} (e : G →₀ ℂ) (v : G → A) :
    (((e.sum fun b a => a • v b : A)) : X) = e.sum fun b a => a • (v b : X) := by
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]

set_option maxHeartbeats 4000000 in

theorem valOne_all : ∀ D : D7, ValOne D := by
  intro D ψ hψ σ S Q G₁ G₂ hG₁ hG₂ hK₁ hK₂ c₁ c₂ hc₁ hc₂ f₁ f₂ hvac φ f hφ hf hTy g hg h₁ hh₁ h₂ hh₂
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
  obtain ⟨A, τ, T, hsm, hτ, hmem, htri, hval, hlast⟩ :=
    GlobalTheory.T.splitPlace_doubleStep_trilinearForm_properties D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ _ _ hT₁' hT₂' φ hφ
  set F : A := ⟨rTrans h₂ f, hmem _ hf' hTy'⟩ with hFdef
  let Φa : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k → GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k →
      SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
    fun a x => ⟨om Q.μ₁ a x Q.Φ₁.1, GlobalTheory.T.weilRepLinearModelGLPair_apply_mem_schwartzBruhatFunctions Q.k _ _ Q.μ₁ a x Q.Φ₁⟩
  let Φb : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k →
      SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x y => ⟨om Q.μ₂ x y Q.Φ₂.1, GlobalTheory.T.weilRepLinearModelGLPair_apply_mem_schwartzBruhatFunctions Q.k _ _ Q.μ₂ x y Q.Φ₂⟩
  obtain ⟨v, hv⟩ : ∃ v : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k → GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k →
      GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → ℂ, ∀ a x y,
      v a x y = S.val c₁ c₂ ((S.s₁.om (g, h₁) ∘ₗ T₁) (Φa a x)) ((S.s₂.om (h₁, h₂) ∘ₗ T₂) (Φb x y)) φ (τ y F).1 1 1 1 :=
    ⟨_, fun _ _ _ => rfl⟩
  have d1 : comb ψ _ _ Q.D₁ (T₁ O₁) = T₁ Q.Φ₁ := (Q.dat₁.2 T₁ hT₁ O₁ Q.Φ₁ hO₁ rfl).symm
  have d2 : comb ψ _ _ Q.D₂ (T₂ O₂) = T₂ Q.Φ₂ := (Q.dat₂.2 T₂ hT₂ O₂ Q.Φ₂ hO₂ rfl).symm
  have KEY : ∀ a x y, S.val c₁ c₂ (comb ψ _ _ Q.D₁ (T₁ O₁)) (comb ψ _ _ Q.D₂ (T₂ O₂)) φ f (g * Q.gl₀ a)
      (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) = v a x y := by
    intro a x y
    rw [hv, d1, d2, val_translate]
    have m1 : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (Q.gl₀ a, Q.gl₁ x) * S.s₁.om (g, h₁) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₀ a g hg, cm₁ x h₁ hh₁]
    have m2 : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (Q.gl₁ x, Q.gl₂ y) * S.s₂.om (h₁, h₂) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₁ x h₁ hh₁, cm₂ y h₂ hh₂]
    have r : rTrans (h₂ * Q.gl₂ y) f = (τ y F).1 := by
      rw [hτ]; funext z; simp only [rTrans, hFdef]; rw [mul_assoc z (Q.gl₂ y) h₂, cm₂ y h₂ hh₂]
    rw [m1, m2, r, Module.End.mul_apply, Module.End.mul_apply]
    exact GlobalTheory.T.doubleStep_local_weil_action_line_characters_cancel D ψ hψ σ S Q _ _ hT₁' hT₂' c₁ c₂ φ _ a x y Q.Φ₁ (Φa a x) Q.Φ₂ (Φb x y) rfl rfl
  haveI i1 : Q.m₁.IsHaarMeasure := Q.haar₁
  haveI i2 : Q.m₂.IsHaarMeasure := Q.haar₂
  have t1 : Q.m₁.IsHaarMeasure := inferInstance
  have t2 := @GlobalTheory.T.symmetricPositions_doubleIntegral_existsUnique Q.k _ _ _ _ _ _ Q.n₀ Q.n₁ Q.n₂ _ _ _ _ _ _ (Q.c+1) (σ+1) hcQ Q.ψk hψc hψ1 Q.ν hsd Q.μ₁ Q.μ₂ Q.open₁ Q.open₂ Q.m₁ Q.haar₁
  haveI := hG₁
  haveI := hG₂
  have ex := fun a => @t2 G₁ hG₁ Q.m₂ Q.haar₂ G₂ hG₂ A _ _ τ hsm T htri F (Φa a 1) Q.Φ₂
  choose z hz _ using ex
  obtain ⟨u, hu1, hu2⟩ := GlobalTheory.T.symmetricDoubleIntegral_finite_combination Q.k Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) hcQ Q.ψk hψc hψ1 Q.ν hsd Q.μ₁ Q.μ₂ Q.m₁ G₁ Q.m₂ G₂
    Q.haar₁ hG₁ Q.haar₂ hG₂ A τ hsm T htri F Q.Φ₁ Q.Φ₂ Q.e₀ z v (fun a _ => hz a)
    (fun a _ x y => by rw [hv]; exact hval (Φa a x) (Φb x y) (τ y F))
  refine ⟨u, fun x => by simpa only [KEY] using hu1 x, ?_⟩

  classical
  let e₂' : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k →₀ ℂ) :=
    fun β => if h : β ∈ Q.A₂ then Q.e₂ ⟨β, h⟩ else 0
  have he₂ : ∀ β ∈ Q.A₂, IsOneComb Q.ψk Q.ν (σ + 1) Q.L₂ β (e₂' β) := by
    intro β hβ; simp only [e₂', dif_pos hβ]; exact Q.one₂ ⟨β, hβ⟩
  have hFty : ∀ j : Q.L₂.J, τ (j : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) F = (Q.L₂.lam j : ℂ) • F := by
    intro j; apply Subtype.ext; rw [hτ, Submodule.coe_smul]; exact hTy' j
  have R := GlobalTheory.T.symmetricDoubleIntegrals_positionOne_eq_cellSum Q.k Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) hcQ Q.ψk hψc Q.cond Q.ν Q.unitVol Q.μ₁ Q.μ₂ Q.open₁ Q.open₂
    Q.m₁ G₁ Q.m₂ G₂ Q.haar₁ hG₁ Q.haar₂ hG₂ hK₁ hK₂ Q.L₀ Q.L₁ Q.L₂ Q.co₁ Q.co₂ Q.le₁ Q.le₂ A τ hsm T htri F hFty
    Q.Φ₁ Q.Φ₂ Q.ty₁ Q.ty₂ Q.α Q.A₁ Q.A₂ Q.cov₁ Q.cov₂ Q.e₀ Q.one₀ e₂' he₂ z (fun a _ => hz a)
  have FIN : ∀ (γ : Q.A₁) (β : Q.A₂), comb (Q.e₂ β) (fun b => app (app T (xi Q.ψk Q.ν Q.μ₁ Q.Φ₁.1 Q.L₁.J 1 Q.α γ.1))
      (xi Q.ψk Q.ν Q.μ₂ Q.Φ₂.1 Q.L₂.J 1 γ.1 β.1) (τ b F)) =
      S.val (aconv [c₁, Q.d₁ γ]) (aconv [c₂, Q.d₂ γ β]) (T₁ O₁) (T₂ O₂) φ (trc ((Q.e₂ β).mapDomain Q.gl₂) f) g h₁ h₂ := by
    intro γ β
    have s1 := GlobalTheory.T.rootExchange_entries_mem_schwartzBruhat Q.k Q.n₁ Q.n₀ (Q.c + 1 + 1) Q.ψk hψc Q.ν Q.unitVol.1 Q.μ₁ Q.Φ₁ Q.L₁.J 1 Q.α γ.1
    have s2 := GlobalTheory.T.rootExchange_entries_mem_schwartzBruhat Q.k Q.n₂ Q.n₁ (Q.c + 1) Q.ψk hψc Q.ν Q.unitVol.1 Q.μ₂ Q.Φ₂ Q.L₂.J 1 γ.1 β.1
    rw [show xi Q.ψk Q.ν Q.μ₁ Q.Φ₁.1 Q.L₁.J 1 Q.α γ.1 = ((⟨_, s1⟩ : SB _) : _ → ℂ) from rfl, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe,
      show xi Q.ψk Q.ν Q.μ₂ Q.Φ₂.1 Q.L₂.J 1 γ.1 β.1 = ((⟨_, s2⟩ : SB _) : _ → ℂ) from rfl, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
    have hl := hlast ⟨_, s1⟩ ⟨_, s2⟩ (Q.d₁ γ) (Q.d₂ γ β) (Q.ent₁ γ) (Q.ent₂ γ β) O₁ O₂ hO₁ hO₂
      ((Q.e₂ β).sum fun b a => a • τ b F)
    have hsum : (((Q.e₂ β).sum fun b a => a • τ b F : A) : GA D S.B'.V → ℂ) =
        rTrans h₂ (trc ((Q.e₂ β).mapDomain Q.gl₂) f) := by
      rw [coe_sum_sub, ← sum_rTrans_trc Q.gl₂ h₂ (fun b => cm₂ b h₂ hh₂)]
      simp only [hτ, hFdef]
    rw [comb_lin τ (T ⟨_, s1⟩ ⟨_, s2⟩) (Q.e₂ β) F, hl, hsum,
      val_translate S _ _ (T₁ O₁) (T₂ O₂) φ _ g h₁ h₂, LinearMap.comp_apply, LinearMap.comp_apply]
  convert hu2 using 1
  rw [R]
  unfold QStep.volJ
  congr 1
  rw [← Finset.sum_coe_sort Q.A₁]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.sum_coe_sort Q.A₂]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [e₂', dif_pos β.2, Subtype.coe_eta]
  rw [← FIN γ β]
  simp only [QStep.w₁, QStep.w₂]
  push_cast
  ring

end GlobalTheory.ValOneAt
end
