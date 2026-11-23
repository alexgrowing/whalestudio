import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBessel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubsetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMoveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelElementOffPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosetFJ

variable {D : D7}

theorem coset_of_places {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (K : Subgroup (GA D W))
    (S : Finset (GlobalTheory.FinPl.Pl D)) :
    (∀ v ∈ S, ∀ g ∈ grpAt W (· = v), Cond dW p x y ψ (· = v) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) →
    ∀ g ∈ grpAt W (· ∈ S), Cond dW p x y ψ (· ∈ S) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ S) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ S) ∧ g = r * k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ g hg _
    have e : g = 1 := GlobalTheory.QRed.grpAt_eq_one (fun v => by simp) hg
    exact ⟨1, one_mem _, one_mem _, 1, one_mem _, one_mem _, by rw [e, one_mul]⟩
  | insert v s hv ih =>
    intro hloc g hg hc
    obtain ⟨g₁, hg₁, g₂, hg₂o, rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have mono : ∀ {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D W}, (∀ w, P w → w ∈ insert v s) → a ∈ grpAt W P →
        a ∈ grpAt W (· ∈ insert v s) := fun hP ha => GlobalTheory.DStepSuppSecond.grpAt_mono hP ha
    have hg₁' : g₁ ∈ grpAt W (· ∈ insert v s) := mono (fun w hw => by simp [hw]) hg₁
    have hg₂ : g₂ ∈ grpAt W (· ∈ insert v s) := by
      have := mul_mem (inv_mem hg₁') hg
      rwa [inv_mul_cancel_left] at this
    have hg₂s : g₂ ∈ grpAt W (· ∈ s) :=
      GlobalTheory.QRed.grpAt_of_off (fun w hw => by rcases Finset.mem_insert.1 hw with h | h; exacts [Or.inl h.symm, Or.inr h])
        hg₂ hg₂o
    have hcomm : g₁ * g₂ = g₂ * g₁ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1 g₁ hg₁ g₂ hg₂o
    have hdisj : ∀ w, w = v → ¬ w ∈ s := fun w hw hws => hv (hw ▸ hws)
    have hg₁o : g₁ ∈ grpOff W (· ∈ s) := GlobalTheory.QRed.grpAt_off hdisj hg₁
    have hc₁ := GlobalTheory.T.of_mul_trivialAtPlaces_subset dW p x y ψ _ _ g₁ g₂ (fun w hw => by simp [hw]) hg₁ hg₂o hcomm hc
    have hc₂ := GlobalTheory.T.of_mul_trivialAtPlaces_subset dW p x y ψ _ _ g₂ g₁ (fun w hw => Finset.mem_insert_of_mem hw) hg₂s hg₁o hcomm.symm
      (hcomm ▸ hc)
    obtain ⟨r₁, hr₁, hr₁a, k₁, hk₁, hk₁a, e₁⟩ := hloc v (Finset.mem_insert_self v s) g₁ hg₁ hc₁
    obtain ⟨r₂, hr₂, hr₂a, k₂, hk₂, hk₂a, e₂⟩ :=
      ih (fun w hw => hloc w (Finset.mem_insert_of_mem hw)) g₂ hg₂s hc₂
    have hk₁r₂ : k₁ * r₂ = r₂ * k₁ := GlobalTheory.SeeSawLastValue.grpAt_comm hdisj hk₁a hr₂a
    refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, mul_mem (mono (fun w hw => by simp [hw]) hr₁a)
      (mono (fun w hw => Finset.mem_insert_of_mem hw) hr₂a), k₁ * k₂, mul_mem hk₁ hk₂,
      mul_mem (mono (fun w hw => by simp [hw]) hk₁a) (mono (fun w hw => Finset.mem_insert_of_mem hw) hk₂a), ?_⟩
    rw [e₁, e₂]
    calc r₁ * k₁ * (r₂ * k₂) = r₁ * (k₁ * r₂) * k₂ := by simp only [mul_assoc]
      _ = r₁ * r₂ * (k₁ * k₂) := by rw [hk₁r₂]; simp only [mul_assoc]

theorem one_coset_decomposition_base : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xFB F σ h'), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  intro D hD T L μ0 hL sc G W M hM F _hF σ h h' g hg hc
  refine coset_of_places (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (lev G (.grid (2 * σ + 2) 0)) G.pl.S0 ?_ g hg hc
  intro v hv g hg hc
  obtain ⟨u, a, ha, hoff⟩ := hc.pt
  obtain ⟨k, hk, hka, hk'⟩ := GlobalTheory.T.exists_level_element_off_place D hD T L μ0 hL sc G W M hM F _hF σ h h' v hv g hg u a ha hoff
  obtain ⟨r, hr, hra, e⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ (xFB F σ h') (· = v) g k u hg hka hk'
  exact ⟨r, hr, hra, k⁻¹, inv_mem hk, inv_mem hka, e⟩

end GlobalTheory.CosetFJ
