import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsLowInv
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Cell

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open GlobalTheory.LieLocFrame (res res_sum res_res)

theorem cellAt_coord_eq_inf : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (U U' : C.Y.X.Opens) (a : ∀ τ : E →+* ℂ, GlobalTheory.ShFam.Cell.Above (Dw.mult τ) → Γ(C.Y.X, U)) (a' : ∀ τ : E →+* ℂ, GlobalTheory.ShFam.Cell.Above (Dw.mult τ) → Γ(C.Y.X, U')), GlobalTheory.ShFam.Cell.CellAt C hV f₀ w U a → GlobalTheory.ShFam.Cell.CellAt C hV f₀ w U' a' → ∀ (τ : E →+* ℂ) (p : GlobalTheory.ShFam.Cell.Above (Dw.mult τ)), C.Y.X.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (a τ p) = C.Y.X.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (a' τ p) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V hV φV f₀ w U U' a a' h h' τ p
  obtain ⟨hU, hUV, hg, φ, fr, t, hx, A, -, htri, hvec, hcell⟩ := h
  obtain ⟨hU', hUV', hg', φ', fr', t', hx', A', -, htri', hvec', hcell'⟩ := h'
  have hgi : genericPoint C.Y.X ∈ U ⊓ U' := ⟨hg, hg'⟩

  have key : ∀ (U₁ : C.Y.X.Opens) (e₁ : U₁ ≤ C.π ⁻¹ᵁ V) (h₁ : genericPoint C.Y.X ∈ U₁),
      (fnOf U₁ h₁).comp (C.π.appLE V U₁ e₁).hom = (C.Y.X.presheaf.germ (C.π ⁻¹ᵁ V) _ (e₁ h₁)).hom.comp (C.π.app V).hom :=
    fun U₁ e₁ h₁ => RingHom.ext fun s => C.Y.X.presheaf.germ_res_apply (homOfLE e₁) _ h₁ _
  have hω : (fnOf U' hg').comp (C.π.appLE V U' hUV').hom = (fnOf U hg).comp (C.π.appLE V U hUV).hom := by
    rw [key, key]
  have hxω : spMap ((fnOf U hg).comp (C.π.appLE V U hUV).hom) ≫ hV.fromSpec ≫ genι Z =
      genericPt C.Y ≫ C.π ≫ genι Z := by
    rw [← spMap_comp_spMap, Category.assoc, hx, htri.1]

  obtain ⟨k₀, hk₀⟩ := GlobalTheory.ShFam.Spread.exists_bc f₀ ((fnOf U hg).comp (C.π.appLE V U hUV).hom) rfl hxω

  have gen : ∀ (U₁ : C.Y.X.Opens) (hU₁ : IsAffineOpen U₁) (e₁ : U₁ ≤ C.π ⁻¹ᵁ V) (h₁ : genericPoint C.Y.X ∈ U₁)
      (φ₁ : c.F →+* Γ(C.Y.X, U₁)) (fr₁ : EigFrame Z φ₁ ((hU₁.fromSpec ≫ C.π) ≫ genι Z))
      (t₁ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)
      (hx₁ : spMap (C.π.appLE V U₁ e₁).hom ≫ hV.fromSpec ≫ genι Z = (hU₁.fromSpec ≫ C.π) ≫ genι Z)
      (A₁ : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U₁))
      (a₁ : ∀ τ : E →+* ℂ, Above (Dw.mult τ) → Γ(C.Y.X, U₁)),
      fr₁.Tri (fnOf U₁ h₁) C.f0 t₁ →
      (∀ τ i, fr₁.vec τ i = ∑ k, A₁ τ i k • res (C.π.appLE V U₁ e₁).hom hx₁ (f₀.vec τ k)) →
      (∀ τ, InCell (A₁ τ) (w τ) (a₁ τ)) →
      (fnOf U₁ h₁).comp (C.π.appLE V U₁ e₁).hom = (fnOf U hg).comp (C.π.appLE V U hUV).hom →
      ∃ M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) C.Y.Fn,
        (∀ i, C.f0.vec τ i = ∑ l, M i l • k₀.vec τ l) ∧ InCell M (w τ) (fnOf U₁ h₁ ∘ a₁ τ) := by
    intro U₁ hU₁ e₁ h₁ φ₁ fr₁ t₁ hx₁ A₁ a₁ htri₁ hvec₁ hcell₁ hω₁
    choose T hT1 hT2 hT3 using htri₁.2.2 τ
    refine ⟨Matrix.of T * (A₁ τ).map (fnOf U₁ h₁), fun i => ?_,
      ((hcell₁ τ).map (fnOf U₁ h₁)).mul_left ⟨fun i k hik => hT2 i k hik, fun i => ?_⟩⟩
    · have e1 := (GlobalTheory.LieMet.isComb_iff (fun k => res (fnOf U₁ h₁) htri₁.1.symm (fr₁.vec τ k)) (T i)
        (C.f0.vec τ i)).1 (hT3 i)
      rw [e1]
      simp only [hvec₁, res_sum, res_res _ hx₁ _ htri₁.1.symm hω₁ hxω, ← hk₀, Matrix.mul_apply, Matrix.of_apply,
        Matrix.map_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    · rw [Matrix.of_apply, hT1 i]
      exact (t₁ τ i).isUnit
  obtain ⟨M, hM, hc⟩ := gen U hU hUV hg φ fr t hx A a htri hvec hcell rfl
  obtain ⟨M', hM', hc'⟩ := gen U' hU' hUV' hg' φ' fr' t' hx' A' a' htri' hvec' hcell' hω
  have hMM : M = M' := by
    ext i l
    have := Fintype.linearIndependent_iff.1 (k₀.linearIndependent_vec τ) (fun l => M i l - M' i l)
      (by simp only [sub_smul, Finset.sum_sub_distrib, ← hM, ← hM', sub_self])
    exact sub_eq_zero.1 (this l)
  subst hMM
  have hp := congrFun (hc.unique hc') p
  apply fnOf_injective (U ⊓ U') hgi
  exact (C.Y.X.presheaf.germ_res_apply (homOfLE inf_le_left) _ hgi (a τ p)).trans
    (hp.trans (C.Y.X.presheaf.germ_res_apply (homOfLE inf_le_right) _ hgi (a' τ p)).symm)

end GlobalTheory.ShFam.Cell
