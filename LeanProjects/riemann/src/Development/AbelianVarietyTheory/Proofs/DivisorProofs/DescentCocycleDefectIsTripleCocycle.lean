import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

namespace GlobalTheory.PolRoot

private theorem gm_charPullTop {X T : Scheme.{0}} (r : T ⟶ X) (t : T) (a : Γ(X, ⊤)ˣ) :
    gm (𝟙 T) t ⊤ (GlobalTheory.CharKer.pullTop r a) = gm r t ⊤ a :=
  (gm_pull (𝟙 T) r t ⊤ trivial a).trans (by rw [Category.id_comp])

theorem defect_tri {X Y T : Scheme.{0}} {f : X ⟶ Y} {M : LB X} {φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ}
    {D : Γ(Triple f, ⊤)ˣ} (h : Defect f M φ D) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f)
    (t : T) (i j k : M.ι) (hi : a t ∈ M.U i) (hj : b t ∈ M.U j) (hk : c t ∈ M.U k) :
    gm (tri f a b c h₁ h₂) t ⊤ D * gm (pullback.lift a c (h₁.trans h₂)) t _ (φ i k) =
      gm (pullback.lift a b h₁) t _ (φ i j) * gm (pullback.lift b c h₂) t _ (φ j k) := by
  have e₁ : tri f a b c h₁ h₂ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) = pullback.lift a b h₁ :=
    pullback.lift_fst _ _ _
  have e₂ : tri f a b c h₁ h₂ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) = pullback.lift b c h₂ :=
    pullback.lift_snd _ _ _
  have e₃ : tri f a b c h₁ h₂ ≫ pr13 f = pullback.lift a c (h₁.trans h₂) := by
    apply pullback.hom_ext
    · rw [pr13, Category.assoc, pullback.lift_fst, reassoc_of% e₁, pullback.lift_fst]
      try rw [pullback.lift_fst]
    · rw [pr13, Category.assoc, pullback.lift_snd, reassoc_of% e₂, pullback.lift_snd]
      try rw [pullback.lift_snd]
  have := h T (tri f a b c h₁ h₂) t i j k
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_fst]; exact hi)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_snd]; exact hj)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₂, pullback.lift_snd]; exact hk)
  rwa [e₁, e₂, e₃] at this

theorem triCocycle_of_defect : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  intro X Y f M hM φ D h T a b c d h₁ h₂ h₃
  refine unit_ext fun t _ => ?_
  obtain ⟨i, hi⟩ := exists_chart hM (a t)
  obtain ⟨j, hj⟩ := exists_chart hM (b t)
  obtain ⟨k, hk⟩ := exists_chart hM (c t)
  obtain ⟨l, hl⟩ := exists_chart hM (d t)
  have e₁ := defect_tri h a b c h₁ h₂ t i j k hi hj hk
  have e₂ := defect_tri h a c d (h₁.trans h₂) h₃ t i k l hi hk hl
  have e₃ := defect_tri h b c d h₂ h₃ t j k l hj hk hl
  have e₄ := defect_tri h a b d h₁ (h₂.trans h₃) t i j l hi hj hl
  rw [map_mul, map_mul, gm_charPullTop, gm_charPullTop, gm_charPullTop, gm_charPullTop]
  apply mul_right_cancel (b := gm (pullback.lift a d ((h₁.trans h₂).trans h₃)) t _ (φ i l))
  rw [_root_.mul_assoc, _root_.mul_assoc, e₂, e₄, ← _root_.mul_assoc, e₁, _root_.mul_left_comm, e₃, _root_.mul_assoc]

end GlobalTheory.PolRoot
