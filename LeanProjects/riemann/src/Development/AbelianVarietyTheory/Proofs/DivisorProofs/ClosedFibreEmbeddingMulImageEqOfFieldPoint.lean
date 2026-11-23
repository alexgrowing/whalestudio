import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem closed_product_image (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G']
    (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme)
    (hl : l ≫ E.H.ι = N.u) (hf : l ≫ E.f = pullback.fst _ _ ≫ fU) (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω)
    (s : Sp Ω ⟶ M.S) (a b c : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (hs : s ≫ M.π = spMap (κ.comp (residue R)))
    (ha : N.Pt s a x.left) (hb : N.Pt s b y.left) (hc : N.Pt s c (x * y).left) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (ca cb : Over.mk (spMap (io.comp κ)) ⟶ E.Y),
      ca.left ≫ E.j = spMap io ≫ a ≫ fU ∧ cb.left ≫ E.j = spMap io ≫ b ≫ fU ∧
      (ca * cb).left ≫ E.j = spMap io ≫ c ≫ fU := by
  obtain ⟨Ω', _, io, e, l', he, hl1, hl2⟩ := E.fib Ω s κ hs
  haveI : IsMonHom e.hom := he
  have hP := isGrpPullback_pullback G' (spMap io ≫ s)
  have hY : IsGrpPullback ((Over.pullback (spMap io ≫ s)).obj G') E.Y (spMap (io.comp κ)) (e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback E.Y (spMap (io.comp κ)))).congr (Category.id_comp _) rfl

  let sec : (Over.mk s ⟶ G') → (Over.mk (𝟙 (Sp Ω')) ⟶ (Over.pullback (spMap io ≫ s)).obj G') := fun z =>
    Over.homMk (pullback.lift (spMap io ≫ z.left) (𝟙 _) (by
      rw [Category.assoc, Over.w z, Category.id_comp]; rfl)) (pullback.lift_snd _ _ _)
  have sec_fst : ∀ z, (sec z).left ≫ pullback.fst G'.hom (spMap io ≫ s) = spMap io ≫ z.left := fun z => pullback.lift_fst _ _ _

  have sec_mul : sec (x * y) = sec x * sec y := by
    let r : Over.mk (𝟙 (Sp Ω') ≫ (spMap io ≫ s)) ⟶ Over.mk s := Over.homMk (spMap io) (by simp)
    have e₁ := hP.2 (Over.mk (𝟙 (Sp Ω'))) (sec x) (sec y) (r ≫ x) (r ≫ y) (sec_fst x).symm (sec_fst y).symm
    rw [← MonObj.comp_mul] at e₁
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [sec_fst, ← e₁]; rfl
    · have h1 := Over.w (sec (x * y))
      have h2 := Over.w (sec x * sec y)
      simp only [Over.mk_hom] at h1 h2
      exact h1.trans h2.symm

  let cp : (Over.mk s ⟶ G') → (Over.mk (spMap (io.comp κ)) ⟶ E.Y) := fun z =>
    Over.homMk ((sec z).left ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) (by
      have h := Over.w (pushPt hY.1.w (sec z))
      simp only [Over.mk_hom, pushPt, Over.homMk_left] at h
      simpa using h)
  have cp_mul : (cp x * cp y).left = (cp (x * y)).left := by
    have e₂ := hY.2 (Over.mk (𝟙 (Sp Ω'))) (sec x) (sec y) (pushPt hY.1.w (sec x)) (pushPt hY.1.w (sec y)) rfl rfl
    rw [← sec_mul] at e₂
    refine Eq.trans ?_ e₂
    exact mul_left_congr (Category.id_comp (spMap (io.comp κ))).symm _ _ _ _ rfl rfl

  have img : ∀ (z : Over.mk s ⟶ G') (d : Sp Ω ⟶ N.U.left), N.Pt s d z.left → (cp z).left ≫ E.j = spMap io ≫ d ≫ fU := by
    intro z d ⟨z₀, h₁, _, h₃⟩
    have hsec : (sec z).left ≫ l' = spMap io ≫ z₀ ≫ l := by
      rw [← cancel_mono E.H.ι, Category.assoc, hl1, sec_fst, Category.assoc, Category.assoc, hl, h₃]
    show ((sec z).left ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) ≫ E.j = _
    rw [Category.assoc, Category.assoc, ← hl2, ← Category.assoc, hsec, Category.assoc, Category.assoc, hf,
      ← Category.assoc z₀, h₁]
  exact ⟨Ω', inferInstance, io, cp x, cp y, img x a ha, img y b hb, by rw [cp_mul]; exact img _ c hc⟩

end GlobalTheory.Mum
