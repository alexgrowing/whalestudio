import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorPull

theorem pow_eq_one_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (N : ℕ) :
    x ^ N = 1 ↔ x' ^ N = 1 := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem pushHom_injective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    Function.Injective (pushHom h T) := by
  intro x y e
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

theorem exists_lift_isTorsionAlong : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (x' : Sp R ⟶ S') (y : Sp R ⟶ S) (N : ℕ) (i₁ : Γ.G.left ⟶ G.left), IsGrpPullback G' G f φ → x' ≫ f = y → Γ.IsTorsionAlong G y N i₁ → ∃ i' : Γ.G.left ⟶ G'.left, i' ≫ φ = i₁ ∧ Γ.IsTorsionAlong G' x' N i' := by
  intro R _ _ T _ Γ S S' G G' _ _ f φ x' y N i₁ h e hT
  subst e
  have hw : i₁ ≫ G.hom = (Γ.G.hom ≫ x') ≫ f := by rw [hT.isOver, Category.assoc]
  have hfst : h.1.lift i₁ (Γ.G.hom ≫ x') hw ≫ φ = i₁ := h.1.lift_fst _ _ _
  have hsnd : h.1.lift i₁ (Γ.G.hom ≫ x') hw ≫ G'.hom = Γ.G.hom ≫ x' := h.1.lift_snd _ _ _
  generalize h.1.lift i₁ (Γ.G.hom ≫ x') hw = i' at hfst hsnd

  have mk : ∀ (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x') ⟶ G'),
      (g.left ≫ φ) ≫ G.hom = Y.hom ≫ x' ≫ f := fun Y g => by
    have w₁ : g.left ≫ G'.hom = Y.hom ≫ x' := Over.w g
    rw [Category.assoc, h.1.w, ← Category.assoc, w₁, Category.assoc]
  refine ⟨i', hfst, ⟨hsnd, ?_, ?_, ?_⟩⟩
  · intro Y a b a₀ b₀ ha hb
    have ea : (Over.homMk (a₀.left ≫ φ) (mk Y a₀) : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G).left = a.left ≫ i₁ := by
      simp [ha, ← hfst]
    have eb : (Over.homMk (b₀.left ≫ φ) (mk Y b₀) : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G).left = b.left ≫ i₁ := by
      simp [hb, ← hfst]
    have e₁ := hT.mul Y a b _ _ ea eb
    have e₂ := h.2 (Over.mk (Y.hom ≫ x')) a₀ b₀ (pushPt h.1.w a₀) (pushPt h.1.w b₀) rfl rfl
    have e₃ := mul_left_congr (Category.assoc Y.hom x' f) (pushPt h.1.w a₀) (pushPt h.1.w b₀)
      (Over.homMk (a₀.left ≫ φ) (mk Y a₀)) (Over.homMk (b₀.left ≫ φ) (mk Y b₀)) rfl rfl
    apply h.1.hom_ext
    · rw [← e₂, e₃, e₁, Category.assoc, hfst]
    · have w₁ : (a₀ * b₀).left ≫ G'.hom = Y.hom ≫ x' := Over.w (a₀ * b₀)
      have w₂ : (a * b).left ≫ Γ.G.hom = Y.hom := Over.w (a * b)
      rw [w₁, Category.assoc, hsnd, ← Category.assoc, w₂]
  · intro Y a b e
    apply hT.inj Y a b
    rw [← hfst, ← Category.assoc, ← Category.assoc, e]
  · intro Y g
    let g₁ : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G := Over.homMk (g.left ≫ φ) (mk Y g)
    have hp : g ^ N = 1 ↔ g₁ ^ N = 1 := by
      rw [← pow_eq_one_congr (Category.assoc Y.hom x' f) (pushHom h (Over.mk (Y.hom ≫ x')) g) g₁ rfl N,
        ← map_pow, ← map_one (pushHom h (Over.mk (Y.hom ≫ x')))]
      exact (pushHom_injective h _).eq_iff.symm
    rw [hp, hT.kernel Y g₁]
    refine exists_congr fun a => ?_
    constructor
    · intro e
      apply h.1.hom_ext
      · rw [Category.assoc, hfst]; exact e
      · have w₁ : g.left ≫ G'.hom = Y.hom ≫ x' := Over.w g
        have w₂ : a.left ≫ Γ.G.hom = Y.hom := Over.w a
        rw [w₁, Category.assoc, hsnd, ← Category.assoc, w₂]
    · intro e
      show a.left ≫ i₁ = g.left ≫ φ
      rw [← e, ← hfst, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.TorPull
