import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem mul_comp_eq_of_isGrpPullback {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G]
    {G₁ : Over S₁} [GrpObj G₁] {G₂ : Over S₂} [GrpObj G₂] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
    {ψ₁ : G₁.left ⟶ G.left} {ψ₂ : G₂.left ⟶ G.left}
    (h₁ : IsGrpPullback G₁ G f₁ ψ₁) (h₂ : IsGrpPullback G₂ G f₂ ψ₂) {T : Scheme.{0}}
    {t₁ : T ⟶ S₁} {t₂ : T ⟶ S₂} (ht : t₁ ≫ f₁ = t₂ ≫ f₂)
    (A₁ B₁ : Over.mk t₁ ⟶ G₁) (A₂ B₂ : Over.mk t₂ ⟶ G₂)
    (hA : A₁.left ≫ ψ₁ = A₂.left ≫ ψ₂) (hB : B₁.left ≫ ψ₁ = B₂.left ≫ ψ₂) :
    (A₁ * B₁).left ≫ ψ₁ = (A₂ * B₂).left ≫ ψ₂ := by
  have key : ∀ (u : T ⟶ S) (e₁ : t₁ ≫ f₁ = u) (e₂ : t₂ ≫ f₂ = u),
      (A₁ * B₁).left ≫ ψ₁ = (A₂ * B₂).left ≫ ψ₂ := by
    intro u e₁ e₂
    have wA : (A₁.left ≫ ψ₁) ≫ G.hom = u := by
      rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w A₁]; exact e₁
    have wB : (B₁.left ≫ ψ₁) ≫ G.hom = u := by
      rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w B₁]; exact e₁
    let a : Over.mk u ⟶ G := Over.homMk (A₁.left ≫ ψ₁) wA
    let b : Over.mk u ⟶ G := Over.homMk (B₁.left ≫ ψ₁) wB
    have p₁ : (a * b).left = (A₁ * B₁).left ≫ ψ₁ := by
      subst e₁
      exact h₁.2 (Over.mk t₁) A₁ B₁ a b rfl rfl
    have p₂ : (a * b).left = (A₂ * B₂).left ≫ ψ₂ := by
      subst e₂
      exact h₂.2 (Over.mk t₂) A₂ B₂ a b hA hB
    exact p₁.symm.trans p₂
  exact key _ ht rfl

theorem etaSecL_add_geom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (a b : LevelMod Dw l)
    (A B C : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ) (hA : A.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ a)
    (hB : B.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ b) (hC : C.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ (a + b)), C = A * B := by
  intro E _ _ _ H Dw l Xo c TF Z X' φ ℓ hℓ Ω _ _ x a b A B C hA hB hC
  obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [← Submodule.Quotient.mk_add] at hC
  let y : Sp Ω ⟶ Xo.XF c := x ≫ i₀ TF.Y Z
  let u : Over.mk y ⟶ 𝟙_ (Over (Xo.XF c)) := Over.homMk y (Category.comp_id y)
  have hψ : ∀ (d : Dw.La) (D : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ),
      D.left = x ≫ etaSecL TF Z φ ℓ hℓ (Submodule.Quotient.mk d) →
      D.left ≫ GlobalTheory.EqvAct.pullψ TF Z φ = (u ≫ TF.Y.oF.eta d).left ≫ TF.Y.m.φ := by
    intro d D hD
    rw [hD, Category.assoc, etaSecL_ψ]
    change _ = ((x ≫ i₀ TF.Y Z) ≫ (TF.Y.oF.eta d).left) ≫ TF.Y.m.φ
    simp only [Category.assoc]
  have ht : (x ≫ ℓ) ≫ φ ≫ (barComp TF.Y Z).ι = y ≫ TF.Y.j := by
    change _ = (x ≫ (TF.Y.j ⁻¹ᵁ barComp TF.Y Z).ι) ≫ TF.Y.j
    rw [Category.assoc, Category.assoc, ← Category.assoc ℓ, hℓ, morphismRestrict_ι]
  have hmul := mul_comp_eq_of_isGrpPullback (GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ) TF.Y.m.cart ht
    A B (u ≫ TF.Y.oF.eta a') (u ≫ TF.Y.oF.eta b') (hψ _ _ hA) (hψ _ _ hB)
  have hC' := hψ _ _ hC
  rw [TF.Y.oF.eta_add a' b', MonObj.comp_mul] at hC'
  ext1
  refine (GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ).1.hom_ext (hC'.trans hmul.symm) ?_
  rw [Over.w C, Over.w (A * B)]

end GlobalTheory.TorsSpec
