import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

namespace GlobalTheory.LieIdImg

open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

theorem genRelR_iff_genThrough {A : Type} [CommRing A] [IsLocalRing A] {B B₀ Y : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K]
    {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Y ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (h : Sp A ⟶ Y) :
    GenRelR w t (LB.pullGen _ _ _ t₀ h) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.GenThrough w ε t t₀ h := by
  constructor
  · intro H
    refine ⟨H.1, fun Z r z p q hp hq => ?_⟩
    have e := ConstGrp.pmaps_of_genRelR ((isGen_iff w).1 hw) hM hM₀ ht (DVR.pullGen_isGen _ _ _ _ ht₀ h) H
      Z r z p q hp hq
    rwa [gm_pullGen', Category.comp_id] at e
  · rintro ⟨h₁, h₂⟩
    refine (genRelR_iff w t _).2 ⟨h₁, fun j j₀ hj₀ hj => ?_⟩
    have e := h₂ _ (𝟙 _) (cpt A) j₀ j hj₀ hj
    simp only [Category.id_comp] at e
    rw [gm_pullGen', Category.id_comp, e]

theorem dualMap_inl {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (r : R) :
    dualMap f (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (f r) := by
  ext <;> simp [dualMap]

theorem dualMap_eps {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    dualMap f DualNumber.eps = DualNumber.eps := by
  ext <;> simp [dualMap]

theorem eq_dualMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (ρ : DualNumber R →+* DualNumber R')
    (h : ∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (f r)) (h' : ρ DualNumber.eps = DualNumber.eps) :
    ρ = dualMap f :=
  (ConstTan.eq_dualMapR f ρ h h').trans (ConstTan.eq_dualMapR f _ (dualMap_inl f) (dualMap_eps f)).symm

theorem lieId_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.LieId W ν v ↔ (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsTanGt ν ∧ LieImg W ν v) := by
  intro E _ _ _ H Dw l Xo c O _ β Y A _ _ _ b a χ W ν v
  refine and_congr_right fun _ => ?_
  let I : Ideal (PowerSeries A) := Ideal.span {PowerSeries.X}
  have hloc : ∀ n, IsLocalRing (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) := fun n =>
    have : IsLocalRing (PowerSeries A ⧸ I ^ (n + 1)) :=
      isLocalRing_quotient_pow (ConstLie.span_X_ne_top (A := A)) n
    ConstTan.isLocalRing_dual _
  have hs : ∀ n, spMap (algebraMap (PowerSeries A ⧸ I ^ (n + 1)) (DualNumber (PowerSeries A ⧸ I ^ (n + 1)))) ≫
      Out.thick (PowerSeries A) I n =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ (epsR (PowerSeries A)).hom := fun n =>
    (ConstLie.spMap_comp' _ _).trans ((congrArg spMap
      (RingHom.ext fun r => (dualMap_inl (Ideal.Quotient.mk (I ^ (n + 1))) r).symm)).trans
        (ConstLie.spMap_comp' _ _).symm)
  constructor
  · intro h n ρ κ vn h₁ h₂ h₃ h₄ _ h₆ x
    have := hloc n
    obtain ⟨vn', k₁, -, k₃⟩ := h n
    obtain rfl := eq_dualMap _ ρ h₁ h₂
    obtain rfl := eq_dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A))) κ h₃ h₄
    have := thick_mono (PowerSeries A) I n
    have hm : Mono (pullback.fst W.t.G.hom (Out.thick (PowerSeries A) I n)) := inferInstance
    obtain rfl : vn = vn' := hm.right_cancellation _ _ (h₆.trans k₁.symm)
    exact (genRelR_iff_genThrough W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt n).t_gen _) vn) (ν.isGen x) _).2 (k₃ x)
  · intro h n
    have := hloc n
    let vn : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (Out.thickObj (PowerSeries A) I n W.t.G).left :=
      pullback.lift (spMap (dualMap (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ v.left) (spMap (algebraMap _ _))
        (by rw [Category.assoc, Over.w v, hs])
    have h' := h n _ _ vn (dualMap_inl _) (dualMap_eps _)
      (dualMap_inl ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))) (dualMap_eps _)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    refine ⟨vn, pullback.lift_fst _ _ _, (Category.assoc _ _ _).symm.trans ((h' 0).1 2), fun x => ?_⟩
    exact (genRelR_iff_genThrough W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt n).t_gen _) vn) (ν.isGen x) _).1 (h' x)

end GlobalTheory.LieIdImg
