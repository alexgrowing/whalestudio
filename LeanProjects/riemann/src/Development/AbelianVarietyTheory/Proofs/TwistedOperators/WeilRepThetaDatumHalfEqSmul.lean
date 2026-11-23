import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMove

open GlobalTheory.SplitHecke

variable {D : D7} {S T : HSp D}

theorem act_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := map_add (actAdd S T g h) x y

theorem act_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := map_nsmul (actAdd S T g h) k x

theorem act_act_inv (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  have := actO_inv_actO g⁻¹ h⁻¹ u
  rwa [inv_inv, inv_inv] at this

theorem isHalf_of_act {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e (actO S T g h u)) :
    IsHalf e u := by
  have := isHalf_actO g⁻¹ h⁻¹ hu
  rwa [actO_inv_actO] at this

theorem isSBHalf_comp {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΨ
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k, hk, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · show Ψ _ = Ψ _
    rw [act_add, act_nsmul]
    exact h2 _ ((hΛ u).1 hu) (isHalf_actO g h hu') _
  · rw [hΛ, act_nsmul]
    exact h3 _ ht

theorem halfInd_act {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (t : WO S T) :
    halfInd e Λ (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  have : (actO S T g h t ∈ Λ ∧ IsHalf e (actO S T g h t)) ↔ (t ∈ Λ ∧ IsHalf e t) :=
    and_congr (hΛ t).symm ⟨isHalf_of_act g h, isHalf_actO g h⟩
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos ht, if_pos (this.2 ht)]
  · rw [if_neg ht, if_neg (fun hh => ht (this.1 hh))]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_theta_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ), (∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → ∀ (g : GA D S) (h : GA D T), (∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) → ∀ c c' : ℂ, c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g⁻¹ h⁻¹ x) = c' * Φ x) → om (g, h) f = (c * c') • f := by
  intro D ψ S T χS χT om hom e Λ f₀ Φ f hth hΘ g h hΛ c c' hc hf₀ hΦ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hΘ
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))
  have hT' : ∀ Ψ, Tm' Ψ = c⁻¹ • om (g, h) (Tm fun t => Ψ (actO S T g h t)) := fun Ψ => rfl
  have hP : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.trans _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hx)
      simp only [act_add, act_act_inv] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.modul _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hy)
      have h2 : ∀ t, symplO S T t (actO S T g⁻¹ h⁻¹ y) = symplO S T (actO S T g h t) y := fun t => by
        rw [← symplO_actO S T g h, act_act_inv]
      simp only [h2] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have h1 := hTm.vac
      rw [one_smul] at h1 ⊢
      have h2 : (fun t => halfInd e Λ (actO S T g h t)) = halfInd e Λ := funext (halfInd_act g h hΛ)
      rw [hT', h2, h1, hf₀, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have e1 : f = Tm Φ := hall Tm hTm
  have e2 : f = Tm' Φ := hall Tm' hP
  have e3 : Φ = c' • fun t => Φ (actO S T g h t) := by
    funext t
    have := hΦ (actO S T g h t)
    rw [actO_inv_actO] at this
    exact this
  rw [hT'] at e2
  have e4 : om (g, h) (Tm fun t => Φ (actO S T g h t)) = c • f := by
    rw [e2, smul_smul, mul_inv_cancel₀ hc, one_smul]
  calc om (g, h) f = om (g, h) (Tm (c' • fun t => Φ (actO S T g h t))) := by rw [← e3, ← e1]
    _ = (c * c') • f := by rw [map_smul, map_smul, e4, smul_smul, mul_comm]

end GlobalTheory.ThetaMove

end
