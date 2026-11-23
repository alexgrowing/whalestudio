import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
namespace GlobalTheory.LBDescent.CocycleTensor

theorem appLE_congr_hom {A B : Scheme.{0}} {g₁ g₂ : A ⟶ B} (hg : g₁ = g₂) (U : B.Opens) (W : A.Opens)
    (e₁ : W ≤ g₁ ⁻¹ᵁ U) (e₂ : W ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U W e₁ = g₂.appLE U W e₂ := by
  subst hg; rfl

theorem germ_appLE_gm {A B : Scheme.{0}} (g : A ⟶ B) {U U' : B.Opens} (W : A.Opens) (e : W ≤ g ⁻¹ᵁ U)
    (hUU' : U ≤ U') (w : A) (hw : w ∈ W) (a : Γ(B, U')ˣ) :
    (A.presheaf.germ W w hw).hom ((g.appLE U W e).hom (res hUU' a).val) = (gm g w U' a).val :=
  (TopCat.Presheaf.germ_res_apply A.presheaf (homOfLE e) w hw ((g.app U).hom (res hUU' a).val)).trans
    ((gm_val g w U (e hw) (res hUU' a)).symm.trans (congrArg Units.val (gm_res g w hUU' (e hw) a)))

set_option maxHeartbeats 1600000 in
theorem cocycle_tensor_of_pointwise : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V V₀ : Y.Opens), IsAffineOpen V₀ →
    ∀ (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
      (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∀ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      (∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b) →
      Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) *
          Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) := by
  intro X Y f _ V V₀ hV₀ h hle c hc e he
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hcond : ∀ z : ↥(pullback f f), f ((pullback.fst f f) z) = f ((pullback.snd f f) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hq : ∀ w : ↥(Triple f), (pullback.snd f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w) = (pullback.fst f f) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) w) := fun w => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have h1 : (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) ≤ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := fun z hz => by
    show f ((pullback.fst f f) z) ∈ V₀
    rw [hcond]; exact hz
  have hleG : ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ≤ (pullback.fst (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) := fun w hw => by
    show f ((pullback.snd f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w)) ∈ V₀
    rw [hq]; exact hw
  have hp1 : pr13 f ≫ (pullback.fst f f) = (pullback.fst (pullback.snd f f) (pullback.fst f f)) ≫ (pullback.fst f f) := pullback.lift_fst _ _ _
  have hp2 : pr13 f ≫ (pullback.snd f f) = (pullback.snd (pullback.snd f f) (pullback.fst f f)) ≫ (pullback.snd f f) := pullback.lift_snd _ _ _
  have h13 : ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ≤ pr13 f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := fun w hw => by
    show f ((pullback.fst f f) (pr13 f w)) ∈ V₀
    have e13 : (pullback.fst f f) (pr13 f w) = (pullback.fst f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w) :=
      (Scheme.Hom.comp_apply _ _ w).symm.trans ((congrArg (fun g => g w) hp1).trans (Scheme.Hom.comp_apply _ _ w))
    rw [e13]
    exact h1 (hleG hw)
  have h2 : (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) ≤ (pullback.fst f f) ⁻¹ᵁ f ⁻¹ᵁ V := h1.trans hle
  have hP := Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)) inferInstance
    (hV₀.preimage f) ((hV₀.preimage f).preimage (pullback.fst f f)) le_rfl hleG
  have e1 : ∀ s : Γ(X, f ⁻¹ᵁ V₀), e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom s) = 1 ⊗ₜ s := fun s => by
    rw [e.symm_apply_eq, he, map_one, _root_.one_mul]
  have e2 : ∀ s : Γ(X, f ⁻¹ᵁ V₀), e.symm (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom s) = s ⊗ₜ 1 := fun s => by
    rw [e.symm_apply_eq, he, map_one, _root_.mul_one]
  let m₁ : Γ(pullback f f, (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ⟶ CommRingCat.of ((Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) :=
    CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))).toRingHom.comp (e.symm.toRingHom.comp ((pullback f f).presheaf.map (homOfLE h).op).hom))
  let m₂ : Γ(pullback f f, (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ⟶ CommRingCat.of ((Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) :=
    CommRingCat.ofHom ((Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))).toRingHom.comp e.symm.toRingHom)
  have cond : (pullback.snd f f).app (f ⁻¹ᵁ V₀) ≫ m₁ = (pullback.fst f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) le_rfl ≫ m₂ := by
    ext s
    show (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom s)) = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) le_rfl).hom s))
    rw [Scheme.Hom.appLE_eq_app, e1, e2]
    simp
  let Ψ := hP.desc m₁ m₂ cond
  have hΨ1 : ∀ y, Ψ.hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom y) = m₁.hom y := fun y =>
    congrArg (fun k => k.hom y) (hP.inl_desc m₁ m₂ cond)
  have hΨ2 : ∀ y, Ψ.hom (((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom y) = m₂.hom y := fun y =>
    congrArg (fun k => k.hom y) (hP.inr_desc m₁ m₂ cond)
  have ka : ∀ a : Γ(X, f ⁻¹ᵁ V₀), ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a) =
      ((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a) := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom a) ((Scheme.Hom.appLE_comp_appLE (pr13 f) (pullback.fst f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) le_rfl h13).trans
      ((appLE_congr_hom hp1 (f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) _ _).trans (Scheme.Hom.appLE_comp_appLE (pullback.fst (pullback.snd f f) (pullback.fst f f)) (pullback.fst f f) (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h1 hleG).symm))
  have kb : ∀ b : Γ(X, f ⁻¹ᵁ V₀), ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b) =
      ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b) := fun b => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom b) ((Scheme.Hom.appLE_comp_appLE (pr13 f) (pullback.snd f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h h13).trans
      ((appLE_congr_hom hp2 (f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) _ _).trans (Scheme.Hom.appLE_comp_appLE (pullback.snd (pullback.snd f f) (pullback.fst f f)) (pullback.snd f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h le_rfl).symm))
  have ra : ∀ a : Γ(X, f ⁻¹ᵁ V₀), ((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a) =
      ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom a) (Scheme.Hom.appLE_map (pullback.fst f f) h1 (homOfLE h).op)
  have hΨ3 : ∀ t, Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (e t)) = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      rw [he, map_mul, map_mul, ka, kb, hΨ1, hΨ2]
      show (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a))) *
        (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b)) = _
      rw [ra, e1, e2]
      simp
  have hABC : ((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val * ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val =
      ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val := by
    apply TopCat.Presheaf.section_ext (Triple f).sheaf ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀))
    intro w hw
    have hw1 : (pullback.fst (pullback.snd f f) (pullback.fst f f)) w ∈ (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) := hleG hw
    have hw13 : pr13 f w ∈ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := h13 hw
    have key := congrArg Units.val (hc w (hle (h1 hw1)))
    show ((Triple f).presheaf.germ ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) w hw).hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val * ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val) =
      ((Triple f).presheaf.germ ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) w hw).hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val)
    rw [Scheme.Hom.app_eq_appLE]
    refine (RingHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (germ_appLE_gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) _ hleG h2 w hw c) (germ_appLE_gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) _ _ hle w hw c)).trans
      ((Units.val_mul _ _).symm.trans (key.trans (germ_appLE_gm (pr13 f) _ h13 hle w hw c).symm))
  have hA : (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val) := by
    have hres : ((pullback f f).presheaf.map (homOfLE h).op).hom (res h2 c).val = (res hle c).val := by
      show ((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback f f).presheaf.map (homOfLE h2).op).hom c.val) =
        ((pullback f f).presheaf.map (homOfLE hle).op).hom c.val
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    exact (congrArg (fun y => (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm y)) hres).symm.trans (hΨ1 _).symm
  have hB : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val) := (hΨ2 _).symm
  have hC : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val) := by
    exact (hΨ3 (e.symm (res hle c).val)).symm.trans (congrArg (fun y => Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom y)) (e.apply_symm_apply _))
  exact (congrArg₂ (· * ·) hA hB).trans ((map_mul Ψ.hom _ _).symm.trans ((congrArg Ψ.hom hABC).trans hC.symm))

end GlobalTheory.LBDescent.CocycleTensor
