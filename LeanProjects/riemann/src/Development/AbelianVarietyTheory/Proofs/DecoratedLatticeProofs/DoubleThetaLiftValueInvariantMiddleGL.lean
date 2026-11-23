import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep.GlMid

variable {D : D7}

theorem comb_right_comm (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (L : Module.End ℂ (WO A S → ℂ))
    (K : WO A S → WO S A' → ℂ) (c : WO S A' →₀ ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' c (fun v' => L (fun u' => K u' v') u) v = L (fun u' => comb ψ S A' c (K u') v) u := by
  have e : (fun u' => comb ψ S A' c (K u') v) =
      ∑ t ∈ c.support, (c t * ψ (symplOH S A' v t)) • (fun u' => K u' (v + t)) := by
    funext u'
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [e, map_sum]
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem comb_left_comm (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (L : Module.End ℂ (WO S A' → ℂ))
    (K : WO A S → WO S A' → ℂ) (c : WO A S →₀ ℂ) (u : WO A S) (v : WO S A') :
    comb ψ A S c (fun u' => L (K u') v) u = L (fun v' => comb ψ A S c (fun u' => K u' v') u) v := by
  have e : (fun v' => comb ψ A S c (fun u' => K u' v') u) =
      ∑ t ∈ c.support, (c t * ψ (symplOH A S u t)) • (fun v' => K (u + t) v') := by
    funext v'
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [e, map_sum]
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem comb_om_comm {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : Om S T}
    (h : IsWeilDatumO ψ S T χS χT ω) (g : GA D S) (g' : GA D T) (c : WO S T →₀ ℂ)
    (hc : ∀ t ∈ c.support, actO S T g g' t = t) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    comb ψ S T c (ω (g, g') f) = ω (g, g') (comb ψ S T c f) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [map_smul, h.om_heis g g' t f hf, hc t ht]

theorem idem_mul {e : AE D} (he : IsSplitIdem D e) : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
  have h1 := he.1
  have h2 := he.2.1
  have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  linear_combination -h1 - 2 * h2 - h3

theorem actO_fix_left {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {a : GA D T} (ha : SuppAt e T a) {t : WO S T}
    (ht : IsHalf (1 - (e + cA D e)) t) : actO S T 1 a t = t := by
  unfold actO
  rw [inv_one, show mt S (1 : GA D S) = 1 from rfl, Matrix.mul_one]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k, mt T a i k * t k j = (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k * t k j := fun k => by
    have ha' := ha i k
    rw [Matrix.sub_apply] at ha'
    have ht' := ht k j
    linear_combination (-(t k j)) * ha' +
      (-((e + cA D e) * (mt T a i k - (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k))) * ht' +
      ((mt T a i k - (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k) * t k j) * idem_mul he
  rw [Finset.sum_congr rfl fun k _ => key k, ← Matrix.mul_apply, Matrix.one_mul]

theorem actO_fix_right {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {a : GA D S} (ha : SuppAt e S a⁻¹) {t : WO S T}
    (ht : IsHalf (1 - (e + cA D e)) t) : actO S T a 1 t = t := by
  unfold actO
  rw [show mt T (1 : GA D T) = 1 from rfl, Matrix.one_mul]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k, t i k * mt S a⁻¹ k j = t i k * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := fun k => by
    have ha' := ha k j
    rw [Matrix.sub_apply] at ha'
    have ht' := ht i k
    linear_combination (-(t i k)) * ha' +
      (-((e + cA D e) * (mt S a⁻¹ k j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j))) * ht' +
      ((mt S a⁻¹ k j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j) * t i k) * idem_mul he
  rw [Finset.sum_congr rfl fun k _ => key k, ← Matrix.mul_apply, Matrix.mul_one]

end GlobalTheory.TriStep.GlMid

namespace GlobalTheory.TriStep
open GlobalTheory.TriStep.GlMid

theorem valK_glMid : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₁ Q.k) (Ξ₁ Ξ₁' : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₁'.1 = om Q.μ₁ 1 g Ξ₁.1 → Ξ₂'.1 = om Q.μ₂ g 1 Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ξ₁ Ξ₁' Ξ₂ Ξ₂' h₁ h₂ hC f _
  obtain ⟨a₁, ha₁⟩ := Witness.exists_isLoc (ofSplit Q.q) Q.F.F₁ g
  have hsplit : IsSplitIdem D (ofSplit Q.q).e := (ofSplit Q.q).split
  have comp₁ : (ofSplit Q.q).IsComp S.χ₁ Q.μ₁⁻¹ := fun x a hxa => by
    have e := Q.comp₁ x a hxa
    rw [MonoidHom.inv_apply, Circle.coe_inv] at e
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e, inv_inv]
  have comp₂ : (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := fun x a hxa => by
    have e := Q.comp₂ x a hxa
    rw [MonoidHom.inv_apply, Circle.coe_inv] at e
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e, inv_inv]
  have hL : ∀ (X₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) (v : WO S.J.W₀ S.B'.A),
      IsThetaFunO ψ S.B.A S.J.W₀ (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ X₂) u v) ∧
      (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' X₂) u v) = S.oma (1, a₁) (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ X₂) u v) := by
    intro X₂ v
    obtain ⟨T₁, hT₁, hT⟩ := hΛ.1 X₂ v
    have e : ∀ X₁ : SB (Matrix Q.n₁ Q.n₀ Q.k), (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ X₂) u v) = T₁ X₁ :=
      fun X₁ => funext (hT X₁ _ (fun _ => rfl))
    rw [e, e]
    refine ⟨hT₁.theta Ξ₁, ?_⟩
    symm
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.B.A S.J.W₀ S.χ₁ S.χ₁ S.oma S.weila Q.μ₁⁻¹ Q.μ₁⁻¹ comp₁ comp₁ Q.n₁ Q.n₀
      Q.F.F₀ Q.F.F₁ T₁ hT₁ 1 1 a₁ g (GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.B.A Q.n₀ Q.F.F₀).1 ha₁ Ξ₁ Ξ₁' ?_
    rw [h₁]
    simp
  have hR : ∀ (X₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (u : WO S.B.A S.J.W₀),
      IsThetaFunO ψ S.J.W₀ S.B'.A (Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂) u) ∧
      Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂') u = S.omb (a₁, 1) (Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂) u) := by
    intro X₁ u
    obtain ⟨T₂, hT₂, hT⟩ := hΛ.2 X₁ u
    have e : ∀ X₂ : SB (Matrix Q.n₂ Q.n₁ Q.k), Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ X₂) u = T₂ X₂ :=
      fun X₂ => funext (hT X₂ _ (fun _ => rfl))
    rw [e, e]
    refine ⟨hT₂.theta Ξ₂, ?_⟩
    symm
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ comp₂ comp₂ Q.n₂ Q.n₁
      Q.F.F₁ Q.F.F₂ T₂ hT₂ a₁ g 1 1 ha₁ (GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.B'.A Q.n₂ Q.F.F₂).1 Ξ₂ Ξ₂' ?_
    rw [h₂]
    simp
  have hA : ∀ t ∈ c₁.support, actO S.B.A S.J.W₀ 1 a₁ t = t := fun t ht =>
    actO_fix_left hsplit ha₁.1 (hc₁ t ht)
  have hB : ∀ t ∈ c₂.support, actO S.J.W₀ S.B'.A a₁ 1 t = t := fun t ht =>
    actO_fix_right hsplit ((GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.J.W₀ Q.n₁ Q.F.F₁).2.2 a₁ g ha₁).1 (hc₂ t ht)

  have hY : ∀ v', IsThetaFunO ψ S.B.A S.J.W₀ (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') := by
    intro v'
    have e : (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') =
        ∑ t ∈ c₂.support, (c₂ t * ψ (symplOH S.J.W₀ S.B'.A v' t)) •
          (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u (v' + t)) := by
      funext u
      simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [e]
    exact GlobalTheory.Core.Rk.Collect.theta_sum _ _ _ fun t => (hL Ξ₂ (v' + t)).1
  have hC' : ∀ u v, biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v =
      S.omb (a₁, 1) (fun v' => S.oma (1, a₁)
        (fun u' => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u' v') u) v := by
    intro u v
    have s1 : ∀ u'', comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') u'') =
        S.omb (a₁, 1) (comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'')) := fun u'' => by
      rw [(hR Ξ₁' u'').2]
      exact comb_om_comm S.weilb a₁ 1 c₂ hB (hR Ξ₁' u'').1
    have s2 : ∀ v' u'', comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'') v' =
        S.oma (1, a₁) (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') u'' := fun v' u'' => by
      have e : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'' =
          fun w => S.oma (1, a₁) (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u w) u'' :=
        funext fun w => congrFun (hL Ξ₂ w).2 u''
      rw [e]
      exact comb_right_comm ψ (S.oma (1, a₁)) (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) c₂ u'' v'
    unfold biComb
    simp only [s1]
    rw [comb_left_comm ψ (S.omb (a₁, 1)) (fun u'' v' => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'') v') c₁ u v]
    refine congrArg (fun F => S.omb (a₁, 1) F v) (funext fun v' => ?_)
    simp only [s2 v']
    rw [comb_om_comm S.weila 1 a₁ c₁ hA (hY v')]

  obtain ⟨b1, -, -, -⟩ := GlobalTheory.SeeSaw.biAct_all D ψ S.B.A S.J.W₀ S.B'.A S.χ₁ S.χ₁ S.χ₂ S.χ₂ S.oma S.omb S.weila S.weilb _ hC
  have hD := b1 (1, a₁)
  obtain ⟨-, -, d3, -⟩ := GlobalTheory.SeeSaw.biAct_all D ψ S.B.A S.J.W₀ S.B'.A S.χ₁ S.χ₁ S.χ₂ S.χ₂ S.oma S.omb S.weila S.weilb _ hD
  have integ : ∀ (h₂ : GA D S.B'.A) (h₁ : GA D S.J.W₀) (h₀ : GA D S.B.A),
      φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v) 0) 0 =
      φ h₀ * S.omb (h₁ * a₁, h₂) (fun v => S.oma (h₀, h₁ * a₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 := by
    intro h₂ h₁ h₀
    have e1 : (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v) 0) =
        S.omb (a₁, 1) (fun v => S.oma (h₀, h₁ * a₁)
          (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) := by
      funext v
      simp only [hC']
      rw [← d3 (h₀, h₁) (a₁, 1) 0 v]
      refine congrArg (fun F => S.omb (a₁, 1) F v) (funext fun v' => ?_)
      change S.oma (h₀, h₁) (S.oma (1, a₁)
        (fun u' => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u' v')) 0 = _
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hinv : ∀ h₂ : GA D S.B'.A, ∀ γ ∈ GQ S.J.W₀, ∀ h₁ : GA D S.J.W₀,
      (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) (γ * h₁) =
      (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) h₁ := by
    intro h₂ γ hγ h₁
    refine congrArg (fun F : GA D S.B.A → ℂ => ∫ h₀ in S.B.vA.𝓕, F h₀ ∂S.B.vA.μ) (funext fun h₀ => ?_)
    have e1 : ∀ v, S.oma (h₀, γ * h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0 =
        S.oma (h₀, h₁) (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0 := fun v => by
      have := GlobalTheory.SeeSawLastValue.om_aut_mul S.weila (one_mem _) hγ h₀ h₁ (GlobalTheory.FrComb.slice_left hC v)
      rwa [one_mul] at this
    simp only [e1]
    have := GlobalTheory.SeeSawLastValue.om_aut_mul S.weilb hγ (one_mem _) h₁ h₂ (GlobalTheory.FrComb.slice_right (b1 (h₀, h₁)) 0)
    rw [one_mul] at this
    exact congrArg (φ h₀ * ·) this
  unfold valK
  congr 1
  funext h₂
  unfold biLift
  simp only [integ h₂]
  exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S.J.W₀ S.J.v0.μ S.J.v0.𝓕 S.J.v0.haar S.J.v0.fund
    (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) (hinv h₂) a₁

end GlobalTheory.TriStep
