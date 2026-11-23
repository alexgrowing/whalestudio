import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LocSplitOp

theorem exists_locOp : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl F) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  intro F _ _ W _ _ Bf κ _ dd ψ hψ G _ act om hsp v p hat hex
  choose! S hS using hex
  refine ⟨S, hS, ?_⟩
  intro u hu Φ hΦ
  have hc : Continuous ψ := hψ.1
  have hw := GlobalTheory.SchrSB.schr_mem_SB ψ hc v (GlobalTheory.LatVac.locCo dd v u) Φ hΦ
  have restS : ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) Φ r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (S Φ) r :=
    fun r hr => ⟨hr.1, by rw [← (hS Φ hΦ).2 r hr]; exact hsp.pres p _ hr.2⟩
  refine GlobalTheory.TensUniq.eq_of_tens_eq v Φ _ _ hΦ fun r hr => ?_
  have hb1 := GlobalTheory.VacBridge.rho_acts_locCo dd ψ v u hu Φ r hr
  have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v)
      (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) r :=
    ⟨hr.1, by rw [← hb1]; exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ _ _ hr.2⟩
  rw [← (hS _ hw).2 r hRw, ← hb1, hsp.impl _ _ _ hr.2, (hS Φ hΦ).2 r hr,
    GlobalTheory.VacBridge.rho_acts_locCo dd ψ v _ (hat u hu) (S Φ) r (restS r hr)]

end GlobalTheory.LocSplitOp
