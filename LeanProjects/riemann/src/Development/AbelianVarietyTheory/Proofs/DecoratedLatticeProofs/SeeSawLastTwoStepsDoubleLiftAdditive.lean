import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsModelCombL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportAconvPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastOneLin

variable {D : D7}

theorem sum_fin {G M : Type*} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem biTheta_left (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO A S →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => C u' v) u) := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  rw [GlobalTheory.BiTransfer.isBiTheta_iff_join d] at hC ⊢
  have e : GlobalTheory.BiTransfer.join d S (fun u v => comb ψ A S c (fun u' => C u' v) u) =
      fun w => ∑ x ∈ c.support, c x * heisO ψ _ S (GlobalTheory.BiTransfer.inlH d S x) (GlobalTheory.BiTransfer.join d S C) w := by
    funext w
    simp only [GlobalTheory.BiTransfer.join_apply, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [GlobalTheory.BiTransfer.symplOH_split d, map_add (GlobalTheory.BiTransfer.fstH d S), map_add (GlobalTheory.BiTransfer.sndH d S),
      GlobalTheory.BiTransfer.fst_inl, GlobalTheory.BiTransfer.snd_inl, add_zero, GlobalTheory.FinTranslate.symplOH_zero_right]
  rw [e]
  exact GlobalTheory.SeeSawFold.theta_sum' c.support _ fun x _ =>
    GlobalTheory.SeeSawFold.theta_const_mul' (c x) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hC _)

theorem biTheta_right (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (C u) v) := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  rw [GlobalTheory.BiTransfer.isBiTheta_iff_join d] at hC ⊢
  have e : GlobalTheory.BiTransfer.join d S (fun u v => comb ψ S A' c (C u) v) =
      fun w => ∑ y ∈ c.support, c y * heisO ψ _ S (GlobalTheory.BiTransfer.inrH d S y) (GlobalTheory.BiTransfer.join d S C) w := by
    funext w
    simp only [GlobalTheory.BiTransfer.join_apply, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [GlobalTheory.BiTransfer.symplOH_split d, map_add (GlobalTheory.BiTransfer.fstH d S), map_add (GlobalTheory.BiTransfer.sndH d S),
      GlobalTheory.BiTransfer.fst_inr, GlobalTheory.BiTransfer.snd_inr, add_zero, GlobalTheory.FinTranslate.symplOH_zero_right, zero_add]
  rw [e]
  exact GlobalTheory.SeeSawFold.theta_sum' c.support _ fun y _ =>
    GlobalTheory.SeeSawFold.theta_const_mul' (c y) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hC _)

theorem biTheta_biComb_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) :=
  biTheta_left hψ hθ (biTheta_right hψ hθ hC c') c

end Theta

theorem aconv_one {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  apply AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G)
  rw [GlobalTheory.QValOuter.aconv_cons, GlobalTheory.QValOuter.aconv_nil, mul_one]

theorem comb_aconv_pair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {E : AE D} (hE : cA D E = E) (hEE : E * E = E)
    (c d : WO S T →₀ ℂ) (hc : ∀ u ∈ c.support, IsHalf (1 - E) u) (hd : ∀ u ∈ d.support, IsHalf E u)
    (f : WO S T → ℂ) : comb ψ S T (aconv [c, d]) f = comb ψ S T c (comb ψ S T d f) := by
  have h := GlobalTheory.QFinLaw.comb_aconv_cons ψ S T c [d] (fun x hx y hy => by
    rw [aconv_one] at hy
    exact GlobalTheory.HeisComb.symplO_half S T (1 - E) E x y (by rw [map_sub, map_one, hE])
      (by rw [sub_mul, one_mul, hEE, sub_self]) (hc x hx) (hd y hy)) f
  rwa [aconv_one] at h

theorem place_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e ∧
      (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  refine ⟨by rw [map_add, cA_cA, add_comm], ?_⟩
  linear_combination h1 + 2 * h2 + h3

theorem lin : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ (ι : Type) (S : Finset ι) (d₁ : ι → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : ι → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ i, ∀ u ∈ (d₁ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → (∀ i, ∀ u ∈ (d₂ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))) = ∑ i ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  intro D c v χ Q hc hv h hr hτ s₁ hs₁ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ ι S d₁ d₂ hd₁ hd₂
  obtain ⟨hE, hEE⟩ := place_idem (D := D) Q.q
  have hL : IsBiTheta c.ψ _ _ _ (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
    obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (Q.s + 1)) (c.X (Q.s + 1)) c.T (c.jac Q.s 0 h).d hc.std
    have hY' : IsThetaFunO c.ψ (c.X (Q.s + 1)) c.T (fun w => Ψ₂ ((c.jac Q.s 0 h).d.ext0 c.T w)) := (hthS Ψ₂).2 hΨ₂
    have hZ' : IsThetaFunO c.ψ (c.B Q.s 0 h).V (c.J Q.s 0 h).W Ψ₁ := hΨ₁
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero s₁ hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes Q.s 0 h).V₀ (c.X Q.s) (c.bes Q.s 0 h).L (c.X (Q.s + 1))
      (c.X (Q.s + 1 + 1)) c.T c.Lz (c.bes Q.s 0 h).o (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hτ (flatBF s₁ Ψ₁) _ hΞ hY'
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X Q.s) := (hc.x Q.s (by omega)).cpt
  have hS : CoCpt (c.X (Q.s + 1)) := (hc.x (Q.s + 1) (by omega)).cpt
  have step : biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) =
      ∑ i ∈ S, biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
    show (GlobalTheory.BiCombStable.biCombL c.ψ _ _ _ c₁ c₂) (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.ProdLocInv.biComb_comp c.ψ _ _ _ c₁ (d₁ i) (aconv [c₁, d₁ i]) c₂ (d₂ i) (aconv [c₂, d₂ i])
      (comb_aconv_pair c.ψ _ _ hE hEE c₁ (d₁ i) hc₁ (hd₁ i)) (comb_aconv_pair c.ψ _ _ hE hEE c₂ (d₂ i) hc₂ (hd₂ i)) _
  rw [step]
  funext h₂
  rw [Finset.sum_apply, sum_fin S (fun i => biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)),
    sum_fin S (fun i => c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) h₂)]
  exact GlobalTheory.SeeSmallPf.biLift_sum hB hoa hob hA hS _ _ hφ
    (fun j => biComb c.ψ _ _ _ (aconv [c₁, d₁ (S.equivFin.symm j)]) (aconv [c₂, d₂ (S.equivFin.symm j)])
      (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))
    (fun j => biTheta_biComb_any hc.std hc.inf hL _ _) h₂

end GlobalTheory.LastOneLin

end
