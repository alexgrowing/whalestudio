import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsionTransfer

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S)
    (hg : T.hom ≫ f = g) (x : T ⟶ G') (x₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  subst hg
  have e : x₀ = pushHom h T x := Over.OverMorphism.ext hx
  rw [e, ← map_pow]
  rfl

theorem torsion_transfer : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (K : Type) [Field K] (ev : V₁ →+* K)
  (Z : Over (Sp K)) [GrpObj Z] (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  ∀ (K₀ : Type) [Field K₀] (e : K₀ →+* K) (Y : Over (Sp K₀)) [GrpObj Y] (φ : Z.left ⟶ Y.left),
  IsGrpPullback Z Y (spMap e) φ →
  ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ X), y ^ n = 1 →
  ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left, q ≫ pullback.fst X.hom (spMap ev) = y.left →
    q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
    ∃ y' : Over.mk (spMap e) ⟶ Y, y' ^ n = 1 ∧ y'.left = q ≫ ψ ≫ φ := by
  intro V₁ _ X _ K _ ev Z _ ψ hψ K₀ _ e Y _ φ hφ n y hy q hq hs
  let P := (Over.pullback (spMap ev)).obj X
  let T0 : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have hqP : q ≫ P.hom = T0.hom := hs
  let qq : T0 ⟶ P := Over.homMk q hqP
  have hP := isGrpPullback_pullback X (spMap ev)

  have h1 := pow_left_of_isGrpPullback hP T0 (spMap ev) (Category.id_comp _) qq y hq.symm n
  have h0 := pow_left_of_isGrpPullback hP T0 (spMap ev) (Category.id_comp _) qq y hq.symm 0
  rw [hy] at h1
  rw [pow_zero, pow_zero] at h0
  have hqn : (qq ^ n).left = (1 : T0 ⟶ P).left := by
    apply pullback.hom_ext
    · exact h1.symm.trans h0
    · exact (Over.w (qq ^ n)).trans (Over.w (1 : T0 ⟶ P)).symm

  have hzw : (q ≫ ψ) ≫ Z.hom = T0.hom := by
    have w := hψ.1.w
    rw [Category.assoc, w, Category.comp_id]; exact hs
  let zz : T0 ⟶ Z := Over.homMk (q ≫ ψ) hzw
  have k1 := pow_left_of_isGrpPullback hψ T0 (𝟙 _) (Category.comp_id _) qq zz rfl n
  have k0 := pow_left_of_isGrpPullback hψ T0 (𝟙 _) (Category.comp_id _) qq zz rfl 0
  rw [pow_zero, pow_zero] at k0
  have hzn : (zz ^ n).left = (1 : T0 ⟶ Z).left := by
    rw [k1, hqn]; exact k0.symm

  have hyw : (q ≫ ψ ≫ φ) ≫ Y.hom = spMap e := by
    have w := hφ.1.w
    rw [Category.assoc, Category.assoc, w, ← Category.assoc ψ, ← Category.assoc q, ← Category.assoc q, hzw]
    exact Category.id_comp _
  refine ⟨Over.homMk (q ≫ ψ ≫ φ) hyw, ?_, rfl⟩
  have m1 := pow_left_of_isGrpPullback hφ T0 (spMap e) (Category.id_comp _) zz (Over.homMk (q ≫ ψ ≫ φ) hyw)
    (by simp [zz]) n
  have m0 := pow_left_of_isGrpPullback hφ T0 (spMap e) (Category.id_comp _) zz (Over.homMk (q ≫ ψ ≫ φ) hyw)
    (by simp [zz]) 0
  rw [pow_zero, pow_zero] at m0
  apply Over.OverMorphism.ext
  rw [m1, hzn, m0]

end GlobalTheory.TorsionTransfer
