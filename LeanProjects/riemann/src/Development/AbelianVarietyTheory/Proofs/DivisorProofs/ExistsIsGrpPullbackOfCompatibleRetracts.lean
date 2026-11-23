import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RetractPullback

theorem exists_isGrpPullback_of_retracts : ∀ {S S' B : Scheme.{0}} (j : S' ⟶ S) (f : S' ⟶ B) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (P : Over B) [GrpObj P] (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback G' P f ψ) (e : G ⟶ G) (e₀ : P ⟶ P) (e' : G' ⟶ G') (he' : IsMonHom e') (h₁ : e'.left ≫ φ = φ ≫ e.left) (h₂ : e'.left ≫ ψ = ψ ≫ e₀.left) (H : Over S) [GrpObj H] (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = e) (C : Over B) [GrpObj C] (k : C ⟶ P) (p : P ⟶ C) (hk : IsMonHom k) (hp : IsMonHom p) (hkp : k ≫ p = 𝟙 C) (hpk : p ≫ k = e₀), ∃ (C' : Over S') (_ : GrpObj C') (a : C'.left ⟶ H.left) (b : C'.left ⟶ C.left), IsGrpPullback C' H j a ∧ IsGrpPullback C' C f b := by
  intro S S' B j f G _ G' _ P _ φ ψ hφ hψ e e₀ e' he' h₁ h₂ H _ i r hi hr hir hri C _ k p hk hp hkp hpk
  have hb := isGrpPullback_pullback C f
  have wk : k.left ≫ P.hom = C.hom := Over.w k
  have wp : p.left ≫ C.hom = P.hom := Over.w p
  have wi : i.left ≫ G.hom = H.hom := Over.w i
  have wr : r.left ≫ H.hom = G.hom := Over.w r
  have we' : e'.left ≫ G'.hom = G'.hom := Over.w e'
  have kp : k.left ≫ p.left = 𝟙 _ := by rw [← Over.comp_left, hkp]; rfl
  have pk : p.left ≫ k.left = e₀.left := by rw [← Over.comp_left, hpk]
  have ir : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir]; rfl
  have ri : r.left ≫ i.left = e.left := by rw [← Over.comp_left, hri]
  have hmw : (pullback.fst C.hom f ≫ k.left) ≫ P.hom = pullback.snd C.hom f ≫ f := by
    rw [Category.assoc, wk]; exact pullback.condition
  let m : pullback C.hom f ⟶ G'.left := hψ.1.lift (pullback.fst C.hom f ≫ k.left) (pullback.snd C.hom f) hmw
  have mψ : m ≫ ψ = pullback.fst C.hom f ≫ k.left := hψ.1.lift_fst _ _ _
  have mh : m ≫ G'.hom = pullback.snd C.hom f := hψ.1.lift_snd _ _ _
  have fix : ∀ {T : Scheme.{0}} (x : T ⟶ pullback C.hom f), x ≫ m ≫ e'.left = x ≫ m := by
    intro T x
    apply hψ.1.hom_ext
    · simp only [Category.assoc, h₂, reassoc_of% mψ, mψ, ← pk, reassoc_of% kp]
    · simp only [Category.assoc, we']
  refine ⟨(Over.pullback f).obj C, inferInstance, m ≫ φ ≫ r.left, pullback.fst C.hom f, ⟨?_, ?_⟩, hb⟩
  · have comm : (m ≫ φ ≫ r.left) ≫ H.hom = pullback.snd C.hom f ≫ j := by
      rw [Category.assoc, Category.assoc, wr, hφ.1.w, reassoc_of% mh]
    refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm (fun s => pullback.lift
        (hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ ψ ≫ p.left) s.snd
        (by simp only [Category.assoc, wp, hψ.1.w, hφ.1.lift_snd_assoc])) ?_ ?_ ?_⟩⟩
    · intro s
      have hm : pullback.lift (hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ ψ ≫ p.left)
          s.snd (by simp only [Category.assoc, wp, hψ.1.w, hφ.1.lift_snd_assoc]) ≫ m =
          hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ e'.left := by
        apply hψ.1.hom_ext
        · simp only [Category.assoc, mψ, h₂, pullback.lift_fst_assoc, pk]
        · simp only [Category.assoc, mh, we', pullback.lift_snd, hφ.1.lift_snd]
      rw [reassoc_of% hm, reassoc_of% h₁, hφ.1.lift_fst_assoc, ← ri]
      simp only [Category.assoc, reassoc_of% ir, ir, Category.comp_id]
    · intro s
      exact pullback.lift_snd _ _ _
    · intro s n hn1 hn2
      have hx : n ≫ m = hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) := by
        apply hφ.1.hom_ext
        · rw [hφ.1.lift_fst, ← hn1]
          calc (n ≫ m) ≫ φ = n ≫ m ≫ e'.left ≫ φ := by rw [reassoc_of% (fix n), Category.assoc]
            _ = _ := by rw [h₁, ← ri]; simp only [Category.assoc]
        · rw [hφ.1.lift_snd, Category.assoc, mh]; exact hn2
      apply pullback.hom_ext
      · rw [pullback.lift_fst, ← reassoc_of% hx, reassoc_of% mψ, kp, Category.comp_id]
      · rw [pullback.lift_snd]; exact hn2
  · intro T x y x₀ y₀ hx hy
    let M : (Over.pullback f).obj C ⟶ G' := Over.homMk m mh
    have pt : ∀ z : T ⟶ (Over.pullback f).obj C, pushPt hψ.1.w (z ≫ M) = pushPt hb.1.w z ≫ k :=
      fun z => Over.OverMorphism.ext (by
        show (z.left ≫ m) ≫ ψ = (z.left ≫ pullback.fst C.hom f) ≫ k.left
        rw [Category.assoc, mψ, Category.assoc])
    have Mmul : (x * y) ≫ M = (x ≫ M) * (y ≫ M) := by
      apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have e1 := hb.2 T x y (pushPt hb.1.w x) (pushPt hb.1.w y) rfl rfl
        have e2 := hψ.2 T (x ≫ M) (y ≫ M) (pushPt hψ.1.w (x ≫ M)) (pushPt hψ.1.w (y ≫ M)) rfl rfl
        rw [← e2, pt, pt, ← MonObj.mul_comp]
        show ((x * y).left ≫ m) ≫ ψ = (pushPt hb.1.w x * pushPt hb.1.w y).left ≫ k.left
        rw [e1, Category.assoc, mψ, Category.assoc]
      · rw [Over.w ((x * y) ≫ M), Over.w ((x ≫ M) * (y ≫ M))]
    have ex : x₀ = pushPt hφ.1.w (x ≫ M) ≫ r := Over.OverMorphism.ext (by
      rw [hx]; show _ = ((x.left ≫ m) ≫ φ) ≫ r.left; simp only [Category.assoc])
    have ey : y₀ = pushPt hφ.1.w (y ≫ M) ≫ r := Over.OverMorphism.ext (by
      rw [hy]; show _ = ((y.left ≫ m) ≫ φ) ≫ r.left; simp only [Category.assoc])
    have e3 := hφ.2 T (x ≫ M) (y ≫ M) (pushPt hφ.1.w (x ≫ M)) (pushPt hφ.1.w (y ≫ M)) rfl rfl
    rw [ex, ey, ← MonObj.mul_comp, Over.comp_left, e3, ← Mmul]
    show ((x * y).left ≫ m) ≫ φ ≫ r.left = _
    simp only [Category.assoc]

end GlobalTheory.RetractPullback
