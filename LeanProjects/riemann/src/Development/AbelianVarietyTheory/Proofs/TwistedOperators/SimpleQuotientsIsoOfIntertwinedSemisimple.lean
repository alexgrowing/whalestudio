import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

theorem simpleQuot_iso_of_intertwined : ∀ (ι Fm Q Q' Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup Pi] [Module ℂ Pi]
  (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (ρ' : ι → Module.End ℂ Q') (C' : Submodule ℂ Q') (σ : ι → Module.End ℂ Pi)
  (β : Fm → Q →ₗ[ℂ] Pi) (β₁ : Q' →ₗ[ℂ] Pi),
  (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ i, β₁ ∘ₗ ρ' i = σ i ∘ₗ β₁) →
  (∀ f, GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker (β f)) → GlobalTheory.RealQuot.rad ρ' C' ≤ LinearMap.ker β₁ → β₁ ≠ 0 →
  (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Q, GlobalTheory.RealQuot.IsStab ρ N → GlobalTheory.RealQuot.rad ρ C ≤ N → N = GlobalTheory.RealQuot.rad ρ C ∨ N = ⊤) →
  (∀ N : Submodule ℂ Q', GlobalTheory.RealQuot.IsStab ρ' N → GlobalTheory.RealQuot.rad ρ' C' ≤ N → N = GlobalTheory.RealQuot.rad ρ' C' ∨ N = ⊤) →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  ∃ e : (Q ⧸ GlobalTheory.RealQuot.rad ρ C) ≃ₗ[ℂ] (Q' ⧸ GlobalTheory.RealQuot.rad ρ' C'),
    ∀ i, e.toLinearMap ∘ₗ GlobalTheory.RealQuot.radAct ρ C i = GlobalTheory.RealQuot.radAct ρ' C' i ∘ₗ e.toLinearMap := by
  intro ι Fm Q Q' Pi _ _ _ _ _ _ ρ C ρ' C' σ β β₁ hβ hβ₁ hkβ hkβ₁ hβ₁0 hspan hQ hQ' hss
  set R := rad ρ C with hRdef
  set R' := rad ρ' C' with hR'def

  have kerStab : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : ι → Module.End ℂ X) (g : X →ₗ[ℂ] Pi),
      (∀ i, g ∘ₗ τ i = σ i ∘ₗ g) → IsStab τ (LinearMap.ker g) := by
    intro X _ _ τ g hg i x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hg i, LinearMap.comp_apply, hx, map_zero]
  set U := LinearMap.range β₁ with hUdef
  have hUs : IsStab σ U := by
    rintro i _ ⟨x, rfl⟩
    exact ⟨ρ' i x, by rw [← LinearMap.comp_apply, hβ₁ i, LinearMap.comp_apply]⟩

  have hUsimple : ∀ Wm : Submodule ℂ Pi, IsStab σ Wm → Wm ≤ U → Wm ≠ ⊥ → Wm = U := by
    intro Wm hW hWU hW0
    have hcs : IsStab ρ' (Wm.comap β₁) := fun i x hx => by
      show β₁ (ρ' i x) ∈ Wm
      rw [← LinearMap.comp_apply, hβ₁ i, LinearMap.comp_apply]
      exact hW i _ hx
    have hcR : R' ≤ Wm.comap β₁ := fun x hx => by
      show β₁ x ∈ Wm
      rw [LinearMap.mem_ker.1 (hkβ₁ hx)]
      exact Wm.zero_mem
    rcases hQ' _ hcs hcR with h | h
    · exfalso
      apply hW0
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨x, rfl⟩ := hWU hw
      have : x ∈ Wm.comap β₁ := hw
      rw [h] at this
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (hkβ₁ this))
    · refine le_antisymm hWU ?_
      rintro _ ⟨x, rfl⟩
      have : x ∈ Wm.comap β₁ := h ▸ Submodule.mem_top
      exact this
  obtain ⟨N', hN's, hc⟩ := hss U hUs
  let P : Pi →ₗ[ℂ] Pi := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U N' hc
  have hPU : ∀ y ∈ U, P y = y := fun y hy =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨y, hy⟩)
  have hPN : ∀ y ∈ N', P y = 0 := fun y hy => by
    exact (congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨y, hy⟩) :)
  have hPmem : ∀ y, P y ∈ U := fun y => (Submodule.linearProjOfIsCompl U N' hc y).2
  have hdec : ∀ y : Pi, ∃ u ∈ U, ∃ n ∈ N', y = u + n := by
    intro y
    have : y ∈ U ⊔ N' := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, n, hn, h⟩ := Submodule.mem_sup.1 this
    exact ⟨u, hu, n, hn, h.symm⟩
  have hPσ : ∀ i y, P (σ i y) = σ i (P y) := by
    intro i y
    obtain ⟨u, hu, n, hn, rfl⟩ := hdec y
    rw [map_add, map_add, map_add, hPU _ (hUs i u hu), hPN _ (hN's i n hn), hPU u hu, hPN n hn, add_zero, add_zero]

  obtain ⟨f, hf⟩ : ∃ f, P ∘ₗ β f ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle : ∀ f, LinearMap.range (β f) ≤ N' := by
      rintro f _ ⟨x, rfl⟩
      obtain ⟨u, hu, n, hn, he⟩ := hdec (β f x)
      have h0 : P (β f x) = 0 := by rw [← LinearMap.comp_apply, hall f, LinearMap.zero_apply]
      rw [he, map_add, hPU u hu, hPN n hn, add_zero] at h0
      rw [he, h0, zero_add]; exact hn
    have hN'top : N' = ⊤ := eq_top_iff.2 (hspan ▸ iSup_le hle)
    have hU0 : U = ⊥ := by
      have := hc.inf_eq_bot
      rwa [hN'top, inf_top_eq] at this
    apply hβ₁0
    ext x
    have : β₁ x ∈ U := LinearMap.mem_range_self β₁ x
    rw [hU0, Submodule.mem_bot] at this
    exact this
  set γ := P ∘ₗ β f with hγdef
  have hγi : ∀ i, γ ∘ₗ ρ i = σ i ∘ₗ γ := by
    intro i; ext x
    show P (β f (ρ i x)) = σ i (P (β f x))
    have h := LinearMap.congr_fun (hβ f i) x
    simp only [LinearMap.comp_apply] at h
    rw [h, hPσ]
  have hRγ : R ≤ LinearMap.ker γ := fun x hx => by
    rw [LinearMap.mem_ker, hγdef, LinearMap.comp_apply, LinearMap.mem_ker.1 (hkβ f hx), map_zero]
  have hkerγ : LinearMap.ker γ = R := by
    rcases hQ _ (kerStab ρ γ hγi) hRγ with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf
  have hkerβ₁ : LinearMap.ker β₁ = R' := by
    rcases hQ' _ (kerStab ρ' β₁ hβ₁) hkβ₁ with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hβ₁0
  have hrangeγ : LinearMap.range γ = U := by
    apply hUsimple
    · rintro i _ ⟨x, rfl⟩
      exact ⟨ρ i x, by rw [← LinearMap.comp_apply, hγi i, LinearMap.comp_apply]⟩
    · rintro _ ⟨x, rfl⟩; exact hPmem _
    · intro h
      apply hf
      ext x
      have : γ x ∈ LinearMap.range γ := LinearMap.mem_range_self γ x
      rw [h, Submodule.mem_bot] at this
      exact this
  let φ := R.liftQ γ hRγ
  let ψ := R'.liftQ β₁ hkβ₁
  have hφi : Function.Injective φ := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hkerγ.le)
  have hψi : Function.Injective ψ := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hkerβ₁.le)
  have hrφ : LinearMap.range φ = LinearMap.range ψ := by
    rw [Submodule.range_liftQ, Submodule.range_liftQ, hrangeγ]
  let e : (Q ⧸ R) ≃ₗ[ℂ] (Q' ⧸ R') :=
    (LinearEquiv.ofInjective φ hφi).trans ((LinearEquiv.ofEq _ _ hrφ).trans (LinearEquiv.ofInjective ψ hψi).symm)
  have he : ∀ x, ψ (e x) = φ x := by
    intro x
    have h1 := LinearEquiv.ofInjective_apply (f := ψ) (h := hψi)
      ((LinearEquiv.ofInjective ψ hψi).symm ((LinearEquiv.ofEq _ _ hrφ) (LinearEquiv.ofInjective φ hφi x)))
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨e, fun i => ?_⟩
  apply Submodule.linearMap_qext
  ext q
  apply hψi
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe]
  rw [he, radAct_mk]
  obtain ⟨q', hq'⟩ := Submodule.Quotient.mk_surjective R' (e (Submodule.Quotient.mk q))
  rw [← hq', radAct_mk]
  have h2 := he (Submodule.Quotient.mk q)
  rw [← hq'] at h2
  simp only [φ, ψ, Submodule.liftQ_apply] at h2 ⊢
  have hb := LinearMap.congr_fun (hβ₁ i) q'
  have hg := LinearMap.congr_fun (hγi i) q
  simp only [LinearMap.comp_apply] at hb hg
  rw [hb, h2]
  exact hg

end GlobalTheory.RealQuot
