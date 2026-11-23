import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.Frames.ChgBC

noncomputable section

namespace GlobalTheory.ArcQ.TanPart

section Mul

variable {B B' Z Z' : Scheme.{0}} {G : Over B} [GrpObj G] {G' : Over B'} [GrpObj G'] {f : B' ⟶ B}
  {φ : G'.left ⟶ G.left}

def IsMul (G : Over B) [GrpObj G] (a b c : Z ⟶ G.left) : Prop :=
  ∃ (s : Z ⟶ B) (x y : Over.mk s ⟶ G), x.left = a ∧ y.left = b ∧ (x * y).left = c

theorem IsMul.left_eq {a b c : Z ⟶ G.left} (h : IsMul G a b c) {s : Z ⟶ B} (x y : Over.mk s ⟶ G)
    (hx : x.left = a) (hy : y.left = b) : (x * y).left = c := by
  obtain ⟨s', x', y', hx', hy', hc⟩ := h
  obtain rfl : s = s' := ((Over.w x).symm.trans (congrArg (· ≫ G.hom) (hx.trans hx'.symm))).trans (Over.w x')
  rw [(Over.OverMorphism.ext (hx.trans hx'.symm) : x = x'), (Over.OverMorphism.ext (hy.trans hy'.symm) : y = y'), hc]

theorem IsMul.pre {a b c : Z ⟶ G.left} (h : IsMul G a b c) (k : Z' ⟶ Z) : IsMul G (k ≫ a) (k ≫ b) (k ≫ c) := by
  obtain ⟨s, x, y, rfl, rfl, rfl⟩ := h
  let D : Over.mk (k ≫ s) ⟶ Over.mk s := Over.homMk k rfl
  exact ⟨k ≫ s, D ≫ x, D ≫ y, rfl, rfl, congrArg (·.left) (MonObj.comp_mul D x y).symm⟩

theorem IsMul.push (hφ : IsGrpPullback G' G f φ) {a b c : Z ⟶ G'.left} (h : IsMul G' a b c) :
    IsMul G (a ≫ φ) (b ≫ φ) (c ≫ φ) := by
  obtain ⟨s, x, y, rfl, rfl, rfl⟩ := h
  exact ⟨s ≫ f, pushPt hφ.1.w x, pushPt hφ.1.w y, rfl, rfl, hφ.2 _ x y _ _ rfl rfl⟩

theorem IsMul.pull (hφ : IsGrpPullback G' G f φ) {a b c : Z ⟶ G'.left} (hb : b ≫ G'.hom = a ≫ G'.hom)
    (hc : c ≫ G'.hom = a ≫ G'.hom) (h : IsMul G (a ≫ φ) (b ≫ φ) (c ≫ φ)) : IsMul G' a b c := by
  let x : Over.mk (a ≫ G'.hom) ⟶ G' := Over.homMk a rfl
  let y : Over.mk (a ≫ G'.hom) ⟶ G' := Over.homMk b hb
  refine ⟨_, x, y, rfl, rfl, hφ.1.hom_ext ?_ ((Over.w (x * y)).trans hc.symm)⟩
  exact (hφ.2 _ x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl).symm.trans (h.left_eq _ _ rfl rfl)

end Mul

section Eps

variable {S : Type} [CommRing S]

theorem fst_alg : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

end Eps

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S]

end Comb

section Gt

open GlobalTheory.TorusModel

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem isZero_of_isAdd {T : Over (Spec (CommRingCat.of A))} {g : Out.GtPt D₀ T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (GlobalTheory.TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := by
    exact (mul_eq_left.1 hb.symm)
  refine ⟨hb1, fun χ => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have C : IsCub (DVR.th D₀ (T := T) y J) := isCub_cubV D₀.cub hJ
  rw [hb1, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

end Gt

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

end ThetaShiftProofs

end GlobalTheory.ArcQ.TanPart
