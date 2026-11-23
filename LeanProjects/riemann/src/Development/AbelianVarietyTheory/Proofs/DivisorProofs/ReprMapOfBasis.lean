import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.ChainPts.AdaptedCoef

theorem repr_map_of_basis {R M M₁ : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁]
    [Module R M₁] {ι κ : Type} (B : Module.Basis ι R M) (B₁ : Module.Basis κ R M₁) (σ : κ → ι)
    (hσ : Function.Injective σ) (q : M →ₗ[R] M₁) (hq : ∀ k, q (B (σ k)) = B₁ k)
    (hz : ∀ j, j ∉ Set.range σ → q (B j) = 0) (u : M) (k : κ) :
    B₁.repr (q u) k = B.repr u (σ k) := by
  classical
  have : (B₁.coord k) ∘ₗ q = B.coord (σ k) := by
    refine B.ext fun j => ?_
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨m, rfl⟩ := hj
      simp [hq, Finsupp.single_apply, hσ.eq_iff]
    · have hne : j ≠ σ k := fun h => hj ⟨k, h.symm⟩
      simp [hz j hj, Finsupp.single_apply, hne]
  exact LinearMap.congr_fun this u

theorem repr_map_eq_zero {R M M₁ : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁]
    [Module R M₁] {ι κ : Type} (B : Module.Basis ι R M) (B₁ : Module.Basis κ R M₁) (σ : κ → ι)
    (i : M₁ →ₗ[R] M) (hi : ∀ k, i (B₁ k) = B (σ k)) (t : M₁) (j : ι) (hj : j ∉ Set.range σ) :
    B.repr (i t) j = 0 := by
  classical
  have : (B.coord j) ∘ₗ i = 0 := by
    refine B₁.ext fun k => ?_
    have hne : σ k ≠ j := fun h => hj ⟨k, h⟩
    simp [hi, Finsupp.single_apply, hne]
  exact LinearMap.congr_fun this t

variable {X : Scheme.{0}} {F F₁ : X.Modules} {r r' : ℕ} {σ : Fin r' → Fin r} {U W : X.Opens}
  {s : Fin r → Γ(F, U)}

theorem repr_q (q : F ⟶ F₁) (hσ : Function.Injective σ) (hs : GlobalTheory.VB.IsFrame s)
    (hz : ∀ j, j ∉ Set.range σ → q.app U (s j) = 0)
    (h₁ : GlobalTheory.VB.IsFrame (fun k => q.app U (s (σ k)))) (h : W ≤ U) (u : Γ(F, W)) (k : Fin r') :
    (h₁.basis h).repr (q.app W u) k = (hs.basis h).repr u (σ k) :=
  repr_map_of_basis (hs.basis h) (h₁.basis h) σ hσ (GlobalTheory.QCoh.appLinear q W)
    (fun k => by
      rw [GlobalTheory.QCoh.appLinear_apply, hs.basis_apply, h₁.basis_apply, app_resM])
    (fun j hj => by
      rw [GlobalTheory.QCoh.appLinear_apply, hs.basis_apply, app_resM, hz j hj, map_zero]) u k

theorem repr_i (i : F₁ ⟶ F) (q : F ⟶ F₁) (hs : GlobalTheory.VB.IsFrame s)
    (hi : ∀ k, i.app U (q.app U (s (σ k))) = s (σ k))
    (h₁ : GlobalTheory.VB.IsFrame (fun k => q.app U (s (σ k)))) (h : W ≤ U) (t : Γ(F₁, W)) (j : Fin r)
    (hj : j ∉ Set.range σ) : (hs.basis h).repr (i.app W t) j = 0 :=
  repr_map_eq_zero (hs.basis h) (h₁.basis h) σ (GlobalTheory.QCoh.appLinear i W)
    (fun k => by
      rw [GlobalTheory.QCoh.appLinear_apply, hs.basis_apply, h₁.basis_apply, app_resM, hi]) t j hj

theorem coef_adapted : ∀ {X : Scheme.{0}} {F F₁ : X.Modules} (i : F₁ ⟶ F) (q : F ⟶ F₁), i ≫ q = 𝟙 F₁ → ∀ {r r' : ℕ} (σ : Fin r' → Fin r), Function.Injective σ → ∀ {U U' : X.Opens} (s : Fin r → Γ(F, U)) (s' : Fin r → Γ(F, U')) (hs : GlobalTheory.VB.IsFrame s) (hs' : GlobalTheory.VB.IsFrame s'), (∀ k, i.app U (q.app U (s (σ k))) = s (σ k)) → (∀ j, j ∉ Set.range σ → q.app U (s j) = 0) → (∀ k, i.app U' (q.app U' (s' (σ k))) = s' (σ k)) → (∀ j, j ∉ Set.range σ → q.app U' (s' j) = 0) → ∀ (h₁ : GlobalTheory.VB.IsFrame (fun k => q.app U (s (σ k)))) (h₁' : GlobalTheory.VB.IsFrame (fun k => q.app U' (s' (σ k)))) (d : Bool) (l : Fin r'), (∀ k, coef d h₁ h₁' k l = coef d hs hs' (σ k) (σ l)) ∧ ∀ j, j ∉ Set.range σ → coef d hs hs' j (σ l) = 0 := by
  intro X F F₁ i q _ r r' σ hσ U U' s s' hs hs' hi hz hi' hz' h₁ h₁' d l
  cases d
  · refine ⟨fun k => ?_, fun j hj => ?_⟩
    · change (h₁.basis inf_le_left).repr (resM F₁ inf_le_right (q.app U' (s' (σ l)))) k =
        (hs.basis inf_le_left).repr (resM F inf_le_right (s' (σ l))) (σ k)
      rw [← app_resM, repr_q q hσ hs hz h₁]
    · change (hs.basis inf_le_left).repr (resM F inf_le_right (s' (σ l))) j = 0
      rw [← hi' l, ← app_resM]
      exact repr_i i q hs hi h₁ _ _ j hj
  · refine ⟨fun k => ?_, fun j hj => ?_⟩
    · change (h₁'.basis inf_le_right).repr (resM F₁ inf_le_left (q.app U (s (σ k)))) l =
        (hs'.basis inf_le_right).repr (resM F inf_le_left (s (σ k))) (σ l)
      rw [← app_resM, repr_q q hσ hs' hz' h₁']
    · change (hs'.basis inf_le_right).repr (resM F inf_le_left (s j)) (σ l) = 0
      rw [← repr_q q hσ hs' hz' h₁', app_resM, hz j hj, map_zero, map_zero, Finsupp.zero_apply]

end GlobalTheory.ChainPts.AdaptedCoef
