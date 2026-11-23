import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
open GlobalTheory.Twist (resM resM_resM app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.VBExt

theorem bijective_add_section {X : Scheme.{0}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (V : X.Opens) (σ : Γ(S.X₃, V) →ₗ[Γ(X, V)] Γ(S.X₂, V)) (hσ : ∀ t, S.g.app V (σ t) = t) :
    Function.Bijective ((appLinear S.f V).coprod σ) := by
  have := hS.mono_f
  have hex (t : Γ(S.X₂, V)) (ht : S.g.app V t = 0) : ∃ u, S.f.app V u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact V t).1 ht
  have hz (u : Γ(S.X₁, V)) : S.g.app V (S.f.app V u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact V _).2 ⟨u, rfl⟩
  have hinj : Function.Injective (appLinear S.f V) := QCoh.injective_app_of_mono S.f V
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, t⟩ h
    rw [LinearMap.coprod_apply, appLinear_apply] at h
    have h3 : t = 0 := by
      have := congrArg (S.g.app V) h
      rwa [map_add, hz, hσ, zero_add, map_zero] at this
    subst h3
    rw [map_zero, add_zero] at h
    have hu : u = 0 := hinj (by rw [map_zero, appLinear_apply]; exact h)
    rw [hu]; rfl
  · intro t
    obtain ⟨u, hu⟩ := hex (t - σ (S.g.app V t)) (by rw [map_sub, hσ, sub_self])
    exact ⟨(u, S.g.app V t), by rw [LinearMap.coprod_apply, appLinear_apply, hu, sub_add_cancel]⟩

theorem isVB_X₂_of_shortExact : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ),
    S.ShortExact → IsVB S.X₁ r → IsVB S.X₃ s → IsVB S.X₂ (r + s) := by
  intro X S r s hS h₁ h₃
  have := hS.epi_g
  refine isVB_of_frames (ι := Fin r ⊕ Fin s) (by simp) fun x => ?_
  obtain ⟨U₁, e₁, hxU₁, he₁⟩ := h₁ x
  obtain ⟨U, hU, hxU, σ, hσc, hσ⟩ := DualExact.exists_local_section S.g h₃ hxU₁
  obtain ⟨U₃, e₃, -, hxU₃, hU₃, he₃⟩ := h₃.exists_affine hxU
  let e : Fin r ⊕ Fin s → Γ(S.X₂, U₃) :=
    Sum.elim (fun i => S.f.app U₃ (resM S.X₁ (hU₃.trans hU) (e₁ i))) fun j => σ U₃ hU₃ (e₃ j)
  refine ⟨U₃, e, hxU₃, isFrame_of_basis (fun V h =>
    ((he₁.basis (h.trans (hU₃.trans hU))).prod (he₃.basis h)).map
      (LinearEquiv.ofBijective _
        (bijective_add_section S hS V (σ V (h.trans hU₃)) (hσ V _)))) fun V h i => ?_⟩
  rcases i with i | j
  · simp only [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, map_zero,
      add_zero, appLinear_apply, IsFrame.basis_apply, e]
    rw [app_resM, app_resM, resM_resM]
  · simp only [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
      LinearMap.inr_apply, LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, map_zero,
      zero_add, appLinear_apply, IsFrame.basis_apply, e]
    exact hσc U₃ V hU₃ h (e₃ j)

end GlobalTheory.VBExt
