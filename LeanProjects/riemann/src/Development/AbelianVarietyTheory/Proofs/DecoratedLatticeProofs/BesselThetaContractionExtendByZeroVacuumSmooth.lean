import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIntegrandContinuousPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsBiSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionQuasiPeriodicRationalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionExtendByZeroDoubleCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroLeftMemCoreLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroRightMemCoreLatticeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

set_option maxHeartbeats 1000000 in
theorem contr_comb_main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → IsBiTheta ψ B.A S B'.A (contr l S vL f₁ f₂) ∧ (∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ), contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) = biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂)) ∧ ∀ (P : Pl D → Prop) (LA : Lat B.A) (LS : Lat S) (LA' : Lat B'.A) (M : Lat B.V₀) (M' : Lat B'.V₀), IsSelfDualC B.A LA → IsSelfDualC S LS → IsSelfDualC B'.A LA' → IsSelfDualC B.V₀ M → IsSelfDualC B'.V₀ M' → (∀ v, P v → (∃ LL, OrthAt B.o M LA LL v) ∧ ∃ LL, OrthAt B'.o M' LA' LL v) → Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → BiVacAt ψ LA LS LA' P (contr l S vL f₁ f₂) := by
  intro D ψ _ ρ σ B B' l S vL f₁ f₂ h₁ h₂
  obtain ⟨hc, hp⟩ := GlobalTheory.T.theta_contraction_integrand_continuous_periodic D ρ σ B B' l S ψ f₁ f₂ h₁ h₂
  have pc := GlobalTheory.Unf.ParCont.parCont D B'.L.rank S.rank vL (WO B.A S × WO S B'.A)
    (fun w p => f₂ ((B'.o.resT S).symm (p.2, w)) * f₁ ((B.o.resS S).symm (p.1, l.κ S w))) hc
    (fun γ hγ w p => hp γ hγ w p.1 p.2)
  have hint : ∀ (u : WO B.A S) (v : WO S B'.A), IntegrableOn
      (fun w => f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w))) vL.𝓕 vL.μ :=
    fun u v => pc.1 (u, v)
  have hcont : Continuous fun p : WO B.A S × WO S B'.A => contr l S vL f₁ f₂ p.1 p.2 := pc.2.1
  obtain ⟨hqL, hqR⟩ := GlobalTheory.T.theta_contraction_quasi_periodic_rational D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  have hsm := GlobalTheory.T.theta_contraction_isBiSmooth D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  have hBi : IsBiTheta ψ B.A S B'.A (contr l S vL f₁ f₂) := {
    cont := hcont
    smooth := hsm
    quasiL := hqL
    quasiR := hqR
    levL := by
      obtain ⟨U, hU, hUf⟩ := h₁.level
      refine ⟨U.comap (extL (S := S) B.o), hU.preimage (continuous_extL B.o), fun a ha hai v => ?_⟩
      funext u
      rw [heis_left, ← extL_apply, hUf _ ha (extL_inf B.o a hai)]
    levR := by
      obtain ⟨U, hU, hUf⟩ := h₂.level
      refine ⟨U.comap (extR (S := S) B'.o), hU.preimage (continuous_extR B'.o), fun a ha hai u => ?_⟩
      funext v
      rw [heis_right, ← extR_apply, hUf _ ha (extR_inf B'.o a hai)] }
  refine ⟨hBi, GlobalTheory.T.theta_contraction_extendByZero_double_combination D ρ σ B B' l S vL ψ f₁ f₂ hint, ?_⟩
  intro P LA LS LA' M M' hLA hLS hLA' hM hM' hor hv₁ hv₂
  have hor1 : ∀ v, P v → ∃ LL, OrthAt B.o M LA LL v := fun v hv => (hor v hv).1
  have hor2 : ∀ v, P v → ∃ LL, OrthAt B'.o M' LA' LL v := fun v hv => (hor v hv).2
  have memL : ∀ a ∈ latO B.A S (LA : Set _) (LS : Set _) P, extL (S := S) B.o a ∈ latO B.V₀ S (M : Set _) (LS : Set _) P :=
    fun a ha => GlobalTheory.T.extendByZero_left_mem_core_lattice D B.V₀ B.A B.L S B.o P LA LS M hLA hLS hM hor1 a ha
  have memR : ∀ b ∈ latO S B'.A (LS : Set _) (LA' : Set _) P, extR (S := S) B'.o b ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P :=
    fun b hb => GlobalTheory.T.extendByZero_right_mem_core_lattice D B'.V₀ B'.A B'.L S B'.o P LA' LS M' hLA' hLS hM' hor2 b hb
  refine ⟨fun v => ⟨?_, ?_, ?_⟩, fun u => ⟨?_, ?_, ?_⟩⟩
  · exact {
      quasi := fun γ u => hqL γ u v
      level := by
        obtain ⟨U, hU, h⟩ := hBi.levL
        exact ⟨U, hU, fun a ha hai => h a ha hai v⟩
      cont := by
        have hh : Continuous fun u : WO B.A S => ((u, v) : WO B.A S × WO S B'.A) := continuous_id.prodMk continuous_const
        exact hcont.comp hh
      smooth := fun k L hL hLf w => by
        have := hsm k L 0 hL continuous_zero hLf (fun _ => by simp) w v
        simpa using this }
  · intro a ha
    funext u
    rw [heis_left, ← extL_apply, map_nsmul, hv₁.2.1 _ (memL a ha)]
  · intro e he a ha hh
    funext u
    rw [heis_left, ← extL_apply, hv₁.2.2 e he _ (memL a ha) (extL_half B.o e a hh)]
  · exact {
      quasi := fun γ v => hqR γ u v
      level := by
        obtain ⟨U, hU, h⟩ := hBi.levR
        exact ⟨U, hU, fun a ha hai => h a ha hai u⟩
      cont := by
        have hh : Continuous fun v : WO S B'.A => ((u, v) : WO B.A S × WO S B'.A) := continuous_const.prodMk continuous_id
        exact hcont.comp hh
      smooth := fun k L hL hLf w => by
        have := hsm k 0 L continuous_zero hL (fun _ => by simp) hLf u w
        simpa using this }
  · intro b hb
    funext v
    rw [heis_right, ← extR_apply, map_nsmul, hv₂.2.1 _ (memR b hb)]
  · intro e he b hb hh
    funext v
    rw [heis_right, ← extR_apply, hv₂.2.2 e he _ (memR b hb) (extR_half B'.o e b hh)]

end GlobalTheory.ContrComb
end
