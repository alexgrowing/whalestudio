import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualKernelLemmas

namespace Formalism.FourierDecayAlt.P.RestrictedDualKernel

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix ComplexOrder

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem cs_on (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X : Submodule ℂ (Ix S → V)) (hP : IsPosOn ρ M X)
    {x y : Ix S → V} (hx : x ∈ X) (hy : y ∈ X) :
    ‖frm ρ M x y‖ ^ 2 ≤ (frm ρ M x x).re * (frm ρ M y y).re := by
  let Ξ : Formalism.FourierDecayAlt.F7.Sesq X :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v : X => frmS ρ M u v)
      (fun u v z => by simp) (fun c u z => by simp) (fun u v z => by simp) (fun c u z => by simp)
  have h := cs_of_pos Ξ (fun m => hP m.1 m.2) ⟨x, hx⟩ ⟨y, hy⟩
  simpa [Ξ, frmS_apply] using h

theorem pos_mul {c u : ℂ} (hc : 0 < c) (hu : 0 ≤ u.re ∧ u.im = 0) : 0 ≤ (c * u).re ∧ (c * u).im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hc
  have hci : c.im = 0 := by linarith
  rw [Complex.mul_re, Complex.mul_im, hci, hu.2]
  constructor
  · nlinarith [hu.1]
  · ring

end Rep

theorem d1cSub : DualityPositiveSubspace := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y X D hD hDX hΦ hP
  have hq : q Y ≠ 0 := hD.2.2.2.2.2
  have hm : ∀ X₂, frm ρ (RR * ins a (TT (↑Y + 1))ᵀ) X₂ X₂ =
      q Y * frm ρ (RR * ins a (TT ↑Y)) (act (PsiP TT q a ↑Y) X₂) (act (PsiP TT q a ↑Y) X₂) := by
    intro X₂
    rw [d1b A S V ρ Ω RR TT q a Y hD X₂ X₂]; field_simp
  refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun hq0 X₂ h₂ => ?_⟩
  · rw [hm, d1a A S V ρ Ω RR TT q a Y hD X₁ X₂]
    refine real_bound _ _ _ _ hq (hP X₁ h₁).2 (hP _ (hΦ X₂ h₂)).2 ?_
    exact cs_on ρ _ X hP h₁ (hΦ X₂ h₂)
  · rw [hm]; exact pos_mul hq0 (hP _ (hΦ X₂ h₂))

theorem lemmaDKSub : LemmaDKSub := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q w L X D hS hD hDX hΦ hP
  have hok := dkDualOK S q w L hD
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ A S QQ q w L hS hD.2.1 hD.2.2.1 hok
  have hkap := Formalism.FourierDecayAlt.P.kappa_formula_holds ℂ S q w L hD.2.1 hD.2.2.1 hok
  have h4 := Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4 S q w L hD.1
  have hk0 : kap q w L ≠ 0 := hdl.2.1
  have hprod : (L.map fun l => qw q w l.pt).prod = kap q w L := by rw [hkap, h4]
  have hm : ∀ X₂, frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ = kap q w L *
      frm ρ (RRw QQ (L ++ w)) (act (Ps QQ q w L) X₂) (act (Ps QQ q w L) X₂) := by
    intro X₂
    simp only [frm]
    rw [pair_act', ← act_mul, ← act_mul, hdl.2.2.2.1, act_csmul, pair_smul_left]
    field_simp
  refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun hq0 X₂ h₂ => ?_⟩
  · rw [hprod, hm, dkStep1 A S V ρ QQ q w L hS hD X₁ X₂]
    refine real_bound _ _ _ _ hk0 (hP X₁ h₁).2 (hP _ (hΦ X₂ h₂)).2 ?_
    exact cs_on ρ _ X hP h₁ (hΦ X₂ h₂)
  · rw [hprod] at hq0; rw [hm]; exact pos_mul hq0 (hP _ (hΦ X₂ h₂))

end Formalism.FourierDecayAlt.P.RestrictedDualKernel

theorem Formalism.FourierDecayAlt.P.duality_positive_subspace : Formalism.FourierDecayAlt.FormPairingAction.DualityPositiveSubspace := Formalism.FourierDecayAlt.P.RestrictedDualKernel.d1cSub
theorem Formalism.FourierDecayAlt.P.dual_kernel_lemma_restricted : Formalism.FourierDecayAlt.FormPairingAction.LemmaDKSub := Formalism.FourierDecayAlt.P.RestrictedDualKernel.lemmaDKSub
