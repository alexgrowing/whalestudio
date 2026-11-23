import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove

def chartPullComp {X Y Z : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (h : Z ⟶ Y) :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h where
  idx J := J
  le J y hy := mem_pull.2 (by simpa using mem_pull.1 hy)
  g y i j hi hj := by
    have hi' : h y ∈ (L.pull F).U i := mem_pull.2 (by simpa using mem_pull.1 hi)
    have hj' : h y ∈ (L.pull F).U j := mem_pull.2 (by simpa using mem_pull.1 hj)
    refine (gm_pull_g L (h ≫ F) (𝟙 Z) y i j hi hj).trans ?_
    refine Eq.trans ?_ (gm_pull_g L F h y i j hi' hj').symm
    rw [Category.id_comp]

theorem lbIso_pull {X Y Z : Scheme.{0}} {L' : LB Y} {L : LB X} {F : Y ⟶ X} (H : LBIso L' (L.pull F)) (h : Z ⟶ Y) :
    LBIso (L'.pull h) (L.pull (h ≫ F)) :=
  LBIso.chartPull (chartPullPull L' h h rfl) (chartPullComp L F h) H

theorem fibreLat_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (z : Sp ℂ ⟶ X'), (Nonempty (SABMap t' t f) → (FibreLat t' z R ↔ FibreLat t (z ≫ f) R)) ∧ ((∀ x, R'.P x = star (R.P x)) → R'.Hm = R.Hm.map (starRingEnd ℂ) → (∀ a x, R'.B a x = star (R.B a (star x))) → FibreLat t' z R → FibreLat t' (spMap (starRingEnd ℂ) ≫ z) R') := by
  intro E _ _ _ H X X' t t' f g Λ _ _ R R' z
  refine ⟨fun ⟨m⟩ => ⟨?_, ?_⟩, fun hP hH hB => ?_⟩
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    obtain ⟨w, hw, -⟩ := m.lin
    obtain ⟨v, hv⟩ := lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw⟩ φ
    have h₁ := pull_isLB t'.PP.isLB φ
    have h₂ := pull_isLB t.PP.isLB (φ ≫ m.cm.F)
    refine ⟨A, inferInstance, φ ≫ m.cm.F, GlobalTheory.ArchMetricCompare.carry u h₁ h₂ hv, χ, hpb.comp m.cart,
      GlobalTheory.ArchMetricCompare.carry_isAH h₁ h₂ hv hAH, fun a p => ?_, hinj, hmem, fun i => i.elim⟩
    show (u.ex (R.B a p)).left ≫ φ ≫ m.cm.F = (u.ex p).left ≫ (φ ≫ m.cm.F) ≫ (t.act.act a).left
    rw [← Category.assoc, hact a p, Category.assoc, Category.assoc, Category.assoc, m.act a]
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    have hp := m.cart.1
    obtain ⟨F, rfl, hw⟩ : ∃ F : A.left ⟶ t'.G.left, F ≫ m.cm.F = φ ∧ F ≫ t'.G.hom = A.hom ≫ z :=
      ⟨hp.lift φ (A.hom ≫ z) (by rw [hpb.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    obtain ⟨w, hw', -⟩ := m.lin
    obtain ⟨v, hv⟩ := (lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw'⟩ F).symm
    have h₁ := pull_isLB t'.PP.isLB F
    have h₂ := pull_isLB t.PP.isLB (F ≫ m.cm.F)
    refine ⟨A, inferInstance, F, GlobalTheory.ArchMetricCompare.carry u h₂ h₁ hv, χ, m.cart.cancel hpb hw,
      GlobalTheory.ArchMetricCompare.carry_isAH h₂ h₁ hv hAH, fun a p => ?_, hinj, hmem, fun i => i.elim⟩
    show (u.ex (R.B a p)).left ≫ F = (u.ex p).left ≫ F ≫ (t'.act.act a).left
    apply hp.hom_ext
    · have e := hact a p
      simp only [Category.assoc] at e ⊢
      rw [m.act a]
      exact e
    · simp only [Category.assoc]
      rw [Over.w (t'.act.act a), hw, ← Category.assoc, ← Category.assoc, Over.w (u.ex _), Over.w (u.ex _)]
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    have h := isGrpPullback_pullback A (spMap (starRingEnd ℂ))
    refine ⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ,
      GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_,
      fun p => ?_, fun i => i.elim⟩
    · rw [hH]
      exact GlobalTheory.ArchMetricCompare.cj_isAH h u hAH
    · show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ =
        (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t'.act.act a).left
      rw [hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ,
        ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]
      simp only [Category.assoc]
    · intro x y e
      rw [hP, hP] at e
      exact hinj (star_injective e)
    · show star p ∈ u.Λ ↔ _
      rw [hmem]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [hP, hx, star_star]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [hP, star_star]⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove
