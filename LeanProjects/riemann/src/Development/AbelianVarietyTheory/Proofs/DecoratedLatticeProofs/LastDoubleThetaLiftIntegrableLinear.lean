import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastDbl

variable {D : D7}

theorem ker_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (a : ℂ) (C : WO A S → WO S X → ℂ) (h₀ : GA D A)
    (h₁ : GA D S) (h₂ : GA D X) :
    GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ = a * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂ := by
  unfold GlobalTheory.SeeSmallPf.ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (a • C) u v) 0) = a • fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : (fun u => (a • C) u v) = a • fun u => C u v := by
      funext u; simp only [Pi.smul_apply]
    rw [e, map_smul]; simp only [Pi.smul_apply]
  rw [e1, map_smul]; simp only [Pi.smul_apply, smul_eq_mul]

theorem biLift_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ (a • C) h₂ = a * biLift oma omX vA vS φ C h₂ := by
  rw [GlobalTheory.SeeSmallPf.biLift_eq, GlobalTheory.SeeSmallPf.biLift_eq]
  have e : ∀ h₀ h₁, φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ =
      a * (φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂) := fun h₀ h₁ => by rw [ker_smul]; ring
  simp only [e, integral_const_mul]

theorem theta_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (a • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w))

theorem sum_fin {G M : Type} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → t.Is → WeilOK (t := t) v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Y : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Y → ∀ φ, IsContAut (c.X j) φ → (∀ X : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ X → ∀ f, IsContAut c.T f → IntegrableOn (fun h' => f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) X Y) ((c.oT (j + 1 + 1) h).emb (h', 1))) c.volT.𝓕 c.volT.μ) ∧ ∀ (G : Type) (s : Finset G) (a : G → ℂ) (X : G → WO (c.V j) (c.V (j + 1)) → ℂ), (∀ g, IsThetaFunO c.ψ _ _ (X g)) → ∑ g ∈ s, a g • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) = c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • X g) Y) := by
  intro D c v t hc ht hW j h Y hY φ hφ
  obtain ⟨χA, χz, χS', χT, omz, omT, omz'', hχV, hWa, hWz, hWX, hWT, hWTb, hWz''⟩ := hW.last j h
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X j) := (hc.x j (by omega)).cpt
  have hS : CoCpt (c.X (j + 1)) := (hc.x (j + 1) (by omega)).cpt
  have hτ := (hW.tau j h).2
  obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d hc.std
  have hY' : IsThetaFunO c.ψ (c.X (j + 1)) c.T (fun w => Y ((c.jac j 0 h).d.ext0 c.T w)) := (hthS Y).2 hY
  have hC : ∀ Z : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ Z →
      IsBiTheta c.ψ (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1)) (c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y) := by
    intro Z hZ
    have hZ' : IsThetaFunO c.ψ (c.B j 0 h).V (c.J j 0 h).W Z := hZ
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero (t.sBF j 0 h) hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
      (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) hτ (flatBF (t.sBF j 0 h) Z) _ hΞ hY'
  refine ⟨fun X hX f hf => GlobalTheory.SeeSmallPf.outer hB hWa hWX (hC X hX) hA hS hc.cpt (c.x j).vol (c.x (j + 1)).vol c.volT
    (c.oT (j + 1 + 1) h) hφ hf, fun G s a X hX => ?_⟩
  have hsum : ∀ (Z : G → WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • Z g) Y =
      ∑ g ∈ s, a g • c.lst j h (v.τ j h) (t.sBF j 0 h) (Z g) Y := by
    intro Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  have hsm : ∀ (b : ℂ) (Z : WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (b • Z) Y =
      b • c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y := by
    intro b Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Pi.smul_apply, smul_eq_mul]
    ring
  funext h₂
  rw [hsum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : ∀ g, a g * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) h₂ =
      c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (a g • X g) Y) h₂ := fun g => by
    rw [hsm]; exact (biLift_smul _ _ _ _ _ _ _ _).symm
  simp only [e1]
  rw [sum_fin s, sum_fin s]
  have e2 : (∑ i : Fin s.card, a (s.equivFin.symm i) • c.lst j h (v.τ j h) (t.sBF j 0 h) (X (s.equivFin.symm i)) Y) =
      ∑ i : Fin s.card, c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y :=
    Finset.sum_congr rfl fun i _ => (hsm _ _).symm
  rw [e2]
  exact (GlobalTheory.SeeSmallPf.biLift_sum hB hWa hWX hA hS (c.x j).vol (c.x (j + 1)).vol hφ
    (fun i => c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y)
    (fun i => hC _ (theta_smul _ (hX _))) h₂).symm

end GlobalTheory.LastDbl

end
