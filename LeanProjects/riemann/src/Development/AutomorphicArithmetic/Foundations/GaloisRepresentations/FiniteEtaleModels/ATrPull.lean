import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
open GlobalTheory.UPel.HT.Hecke.PullHecke
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA mem_heckeSubA)

attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Gal.FiniteEtaleModels

theorem trPull : TrPull := by
  intro q _ D R _ b f c k N S S' s s' j o o' ψ o₁ o₁' m m' hT
  obtain ⟨hmon, hact, heta, hgal, ⟨hlb⟩, hck⟩ := hT
  have hc1 : m.φ ≫ o.A.hom = o₁.A.hom ≫ j := m.cart.1.w
  have hc2 : m'.φ ≫ o'.A.hom = o₁'.A.hom ≫ j := m'.cart.1.w
  have hψw : ψ.left ≫ o'.A.hom = o.A.hom := Over.w ψ
  let l : o₁.A.left ⟶ o₁'.A.left := m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom
    (by rw [Category.assoc, hψw, hc1])
  have hl1 : l ≫ m'.φ = m.φ ≫ ψ.left := m'.cart.1.lift_fst _ _ _
  have hl2 : l ≫ o₁'.A.hom = o₁.A.hom := m'.cart.1.lift_snd _ _ _
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk l hl2
  have hψ₁ : ψ₁.left = l := rfl
  have hext : ∀ {Z : Scheme} (u v : Z ⟶ o₁'.A.left), u ≫ m'.φ = v ≫ m'.φ →
      u ≫ o₁'.A.hom = v ≫ o₁'.A.hom → u = v := fun u v h1 h2 => m'.cart.1.hom_ext h1 h2
  have hl1' : ∀ {Z : Scheme} (u : Z ⟶ o₁.A.left), u ≫ l ≫ m'.φ = u ≫ m.φ ≫ ψ.left := by
    intro Z u
    rw [hl1]
  have hl2' : ∀ {Z : Scheme} (u : Z ⟶ o₁.A.left), u ≫ l ≫ o₁'.A.hom = u ≫ o₁.A.hom := by
    intro Z u
    rw [hl2]
  refine ⟨ψ₁, ⟨?_, ?_, ?_, ?_, ?_, hck⟩, hl1⟩
  · apply isMonHom_of_mul
    intro T x y
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    apply hext
    · have h1 := m.cart.2 T x y (pushPt hc1 x) (pushPt hc1 y) rfl rfl
      have h2 := m'.cart.2 T (x ≫ ψ₁) (y ≫ ψ₁) (pushPt hc1 x ≫ ψ) (pushPt hc1 y ≫ ψ)
        (by simp only [Over.comp_left, hψ₁, Category.assoc, hl1]; rfl)
        (by simp only [Over.comp_left, hψ₁, Category.assoc, hl1]; rfl)
      rw [Category.assoc, hl1', ← h2, ← MonObj.mul_comp, Over.comp_left, h1, Category.assoc]
    · simp only [Category.assoc, hl2', Over.w]
  · intro a
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    have hA : (o.act.act a).left ≫ ψ.left = ψ.left ≫ (o'.act.act a).left := by
      rw [← Over.comp_left, hact a, Over.comp_left]
    apply hext
    · rw [Category.assoc, hl1', ← Category.assoc, m.act a, Category.assoc, hA,
        Category.assoc, m'.act a, ← Category.assoc l, hl1, Category.assoc]
    · simp only [Category.assoc, hl2', Over.w, hl2]
  · intro x
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    apply hext
    · rw [m'.eta x, heta x, Over.comp_left, Category.assoc, hl1', ← Category.assoc (o₁.eta (f x)).left,
        m.eta (f x), Category.assoc]
    · simp only [Category.assoc, hl2', Over.w]
  · have hkey : ∀ y : D.La, (transl (o₁.eta y)).left ≫ m.φ = m.φ ≫ (transl (o.eta y)).left := by
      intro y
      let e : Over.mk (o₁.A.hom ≫ j) ⟶ o.A := pushPt hc1 (𝟙 o₁.A)
      have he : e.left = m.φ := by simp [e, pushPt]
      have h1 := m.cart.2 o₁.A (𝟙 o₁.A) (toUnit o₁.A ≫ o₁.eta y) e (toUnit _ ≫ o.eta y) rfl
        (by simp [m.eta])
      have h2 : e ≫ transl (o.eta y) = e * (toUnit _ ≫ o.eta y) := by
        simp only [transl, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
      calc (transl (o₁.eta y)).left ≫ m.φ = (e * (toUnit _ ≫ o.eta y)).left := by unfold transl; exact h1.symm
        _ = (e ≫ transl (o.eta y)).left := by rw [h2]
        _ = m.φ ≫ (transl (o.eta y)).left := by rw [Over.comp_left, he]
    have hpb : IsPullback m.φ ψ₁.left ψ.left m'.φ :=
      IsPullback.of_bot (by rw [hψ₁, hl2, hψw]; exact m.cart.1) hl1.symm m'.cart.1
    refine isGaloisCover_of_isPullback hgal hpb ?_ ?_ ?_ ?_ ?_ ?_
    · show (transl (1 : 𝟙_ (Over S') ⟶ o₁.A)).left = _
      rw [transl_one]
      rfl
    · intro a a'
      simp only [Subgroup.coe_mul, transl_mul, Over.comp_left]
    · intro a a' h
      exact Subtype.ext (transl_injective h)
    · rintro ⟨h, x, rfl⟩
      simp only [hψ₁]
      apply hext
      · rw [Category.assoc, hl1', ← Category.assoc, hkey, Category.assoc,
          hgal.inv ⟨o.eta (N • f x), mem_heckeSubA o f N x⟩, hl1]
      · simp only [Category.assoc, hl2', Over.w, hl2]
    · rintro ⟨h, x, rfl⟩
      exact ⟨⟨o.eta (N • f x), mem_heckeSubA o f N x⟩, hkey _⟩
    · rintro ⟨h, x, rfl⟩
      exact ⟨⟨o₁.eta (N • f x), mem_heckeSubA o₁ f N x⟩, hkey _⟩
  · have hsq : sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply grpScheme_square_hom_ext
      · have e1 : m'.φ₂ ≫ (fst o'.A o'.A).left = (fst o₁'.A o₁'.A).left ≫ m'.φ := m'.sq.1
        have e2 : m.φ₂ ≫ (fst o.A o.A).left = (fst o₁.A o₁.A).left ≫ m.φ := m.sq.1
        calc (sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left
            = (sq2 ψ₁ ≫ (fst o₁'.A o₁'.A).left) ≫ m'.φ := by
              rw [Category.assoc, e1, Category.assoc]
          _ = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
              rw [grpSchemeSquareProductMap_comp_fst, Category.assoc, hψ₁, hl1]
          _ = (m.φ₂ ≫ (fst o.A o.A).left) ≫ ψ.left := by
              rw [e2, Category.assoc]
          _ = (m.φ₂ ≫ sq2 ψ) ≫ (fst o'.A o'.A).left := by
              rw [Category.assoc, Category.assoc, grpSchemeSquareProductMap_comp_fst]
      · have e1 : m'.φ₂ ≫ (snd o'.A o'.A).left = (snd o₁'.A o₁'.A).left ≫ m'.φ := m'.sq.2
        have e2 : m.φ₂ ≫ (snd o.A o.A).left = (snd o₁.A o₁.A).left ≫ m.φ := m.sq.2
        calc (sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left
            = (sq2 ψ₁ ≫ (snd o₁'.A o₁'.A).left) ≫ m'.φ := by
              rw [Category.assoc, e1, Category.assoc]
          _ = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
              rw [grpSchemeSquareProductMap_comp_snd, Category.assoc, hψ₁, hl1]
          _ = (m.φ₂ ≫ (snd o.A o.A).left) ≫ ψ.left := by
              rw [e2, Category.assoc]
          _ = (m.φ₂ ≫ sq2 ψ) ≫ (snd o'.A o'.A).left := by
              rw [Category.assoc, Category.assoc, grpSchemeSquareProductMap_comp_snd]
    have hL1 : (Hecke.lbPow o₁.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hL0 : (Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hL1 (pull_isLB o₁'.isLB (sq2 ψ₁))).1 ?_⟩
    rw [cls_heckePow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB,
      (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol, GlobalTheory.CechPic.cls_pull o.isLB,
      (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol, GlobalTheory.CechPic.cls_pull o'.isLB,
      ← GlobalTheory.CechPic.pull_comp, hsq, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _),
      ← (GlobalTheory.CechPic.cls_eq_iff hL0 (pull_isLB o'.isLB (sq2 ψ))).2 hlb,
      cls_heckePow o.isLB, map_nsmul]

end UpperTheory.Gal.FiniteEtaleModels
