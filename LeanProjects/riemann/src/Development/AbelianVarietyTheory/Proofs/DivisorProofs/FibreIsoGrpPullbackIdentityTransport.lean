import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreTransport

theorem exists_compare {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ G₂ : Over S'} [GrpObj G₁] [GrpObj G₂]
    {f₁ f₂ : S' ⟶ S} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁)
    (h₂ : IsGrpPullback G₂ G f₂ φ₂) (hf : f₁ = f₂) :
    ∃ e : G₁.left ⟶ G₂.left, IsGrpPullback G₁ G₂ (𝟙 S') e ∧ e ≫ φ₂ = φ₁ := by
  subst hf
  refine ⟨h₂.1.lift φ₁ G₁.hom h₁.1.w, IsGrpPullback.cancel h₂ ?_ ?_, h₂.1.lift_fst _ _ _⟩
  · rw [h₂.1.lift_fst, Category.id_comp]; exact h₁
  · rw [h₂.1.lift_snd]; simp

theorem isGrpPullback_of_isIso {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ⟶ G₂)
    [IsMonHom e] [IsIso e] : IsGrpPullback G₁ G₂ (𝟙 S) e.left := by
  haveI : IsIso e.left := inferInstanceAs (IsIso ((Over.forget S).map e))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let k : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = k ≫ x ≫ e := Over.OverMorphism.ext (by simp [k, hx])
  have ey : y₀ = k ≫ y ≫ e := Over.OverMorphism.ext (by simp [k, hy])
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [k]

theorem transport : ∀ (V V₁ K : Type) [CommRing V] [CommRing V₁] [Field K] (B : Over (Sp V)) [GrpObj B] (ρ : V →+* V₁) (ev : V₁ →+* K) (σ : K ≃+* K) (f₁ : (Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B) ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj ((Over.pullback (spMap ρ)).obj B)), IsMonHom f₁ → IsIso f₁ → ∃ f : ((Over.pullback (spMap (ev.comp ρ))).obj B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B) (𝟙 _) f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B)).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj B).left), y ≫ pullback.fst B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) ≫ pullback.fst B.hom (spMap ρ) → y ≫ pullback.snd B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) → x ≫ f₁.left ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap (σ.toRingHom.comp ev)) ≫ pullback.fst B.hom (spMap ρ) = y ≫ f ≫ pullback.fst B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  intro V V₁ K _ _ _ B _ ρ ev σ f₁ hm hi
  have sp : ∀ t : V₁ →+* K, spMap (t.comp ρ) = spMap t ≫ spMap ρ := fun t => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have two : ∀ t : V₁ →+* K, IsGrpPullback ((Over.pullback (spMap t)).obj ((Over.pullback (spMap ρ)).obj B)) B
      (spMap t ≫ spMap ρ) (pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap t) ≫ pullback.fst B.hom (spMap ρ)) :=
    fun t => (isGrpPullback_pullback _ (spMap t)).comp (isGrpPullback_pullback B (spMap ρ))
  obtain ⟨e₀, h₀, w₀⟩ := exists_compare (isGrpPullback_pullback B (spMap (ev.comp ρ))) (two ev) (sp ev)
  obtain ⟨e₁, h₁, w₁⟩ := exists_compare (two (σ.toRingHom.comp ev))
    (isGrpPullback_pullback B (spMap (σ.toRingHom.comp (ev.comp ρ)))) (sp (σ.toRingHom.comp ev)).symm
  refine ⟨e₀ ≫ f₁.left ≫ e₁, ?_, fun T x y hy₁ hy₂ => ?_⟩
  · have := h₀.comp ((isGrpPullback_of_isIso f₁).comp h₁)
    rwa [Category.id_comp, Category.id_comp] at this
  · have hx : x = y ≫ e₀ := by
      refine (two ev).1.hom_ext ?_ ?_
      · rw [Category.assoc, w₀]; exact hy₁.symm
      · rw [Category.assoc, h₀.1.w, Category.comp_id]; exact hy₂.symm
    rw [hx, Category.assoc, Category.assoc, Category.assoc, w₁]

end GlobalTheory.FibreTransport
