import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.TrStab

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left']

theorem eq_one_of_push {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) {T : Over S'} (x : T ⟶ G')
    (hx : x.left ≫ θ = T.hom ≫ f ≫ η[G].left) : x = 1 := by
  ext
  apply h.1.hom_ext
  · rw [hx, one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  · rw [Over.w x, Over.w (1 : T ⟶ G')]

theorem push_one {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) (T : Over S') :
    (1 : T ⟶ G').left ≫ θ = T.hom ≫ f ≫ η[G].left := by
  rw [one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]

end GlobalTheory.UPel.HT.ES.TrStab

namespace GlobalTheory.UPel.HT.ES

open TrStab

theorem kerStableAt_iff_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ hB hψ
  constructor
  · intro h T' σ hσ g hg a
    rw [Category.comp_id] at hσ
    subst hσ
    have hG : pushPt m.cart.1.w g ≫ ψ = 1 := by
      ext
      rw [one_left', Over.comp_left]
      show (g.left ≫ m.φ) ≫ ψ.left = _
      rw [Category.assoc, hψ, ← Category.assoc, ← Over.comp_left, hg, push_one hB]
      rfl
    have h2 := h (Over.mk (T'.hom ≫ t)) T'.hom rfl (pushPt m.cart.1.w g) hG a
    apply eq_one_of_push hB
    have e := congrArg Over.Hom.left h2
    rw [one_left', Over.comp_left, Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc]
    rw [← hψ, ← Category.assoc (o₁.act.act a).left, m.act a, Category.assoc]
    exact e
  · intro h T0 σ hσ g hg a
    have w : g.left ≫ o.A.hom = σ ≫ t := by rw [Over.w g, hσ]
    let g₁ : Over.mk σ ⟶ o₁.A := Over.homMk (m.cart.1.lift g.left σ w) (m.cart.1.lift_snd _ _ _)
    have hg₁ : g₁.left ≫ m.φ = g.left := m.cart.1.lift_fst _ _ _
    have h1 : g₁ ≫ ψ₁ = 1 := by
      apply eq_one_of_push hB
      rw [Over.comp_left, Category.assoc, ← hψ, ← Category.assoc, hg₁, ← Over.comp_left, hg, one_left', ← hσ, Category.assoc]
      rfl
    have h2 := h (Over.mk σ) σ (Category.comp_id σ) g₁ h1 a
    ext
    rw [one_left', Over.comp_left, Over.comp_left, ← hg₁, Category.assoc, ← Category.assoc m.φ (o.act.act a).left,
      ← m.act a]
    simp only [Category.assoc]
    rw [hψ]
    have e : (g₁ ≫ o₁.act.act a ≫ ψ₁).left ≫ θ = (1 : Over.mk σ ⟶ B₁).left ≫ θ := by rw [h2]
    rw [push_one hB] at e
    simp only [Over.comp_left, Category.assoc] at e
    rw [e, ← hσ, Category.assoc]
    rfl

end GlobalTheory.UPel.HT.ES
