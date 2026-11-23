import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup

noncomputable section

namespace GlobalTheory.ConstEig

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

section Transport

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLie

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {D : DegPre R} {D₀ : DegPre R₀}
  {φ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {e : D₀.X → D.X}

theorem tr_comp {T : Over (Sp R)} {T₀ T₁ : Over (Sp R₀)} {h : T.left ⟶ T₁.left} {g : GtPt D T} {g₀ : GtPt D₀ T₀}
    {g₁ : GtPt D₀ T₁} (H : Tr w e h g g₁) (ρ : T₁ ⟶ T₀) (P : GtPt.IsPull ρ.left g₀ g₁) :
    Tr w e (h ≫ ρ.left) g g₀ := fun x => by
  have hb : ρ ≫ g₀.b = g₁.b := (Over.OverMorphism.ext P.1).symm
  refine ⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [(H x).1, Category.assoc, ConstTanRed.comp_gtφT D₀ ρ g₀.b g₁.b hb]
  · refine Eq.trans ?_ ((H x).2 Z r z J J' hJ hJ')
    rw [← Category.assoc]
    exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (P.2 x) (r ≫ h)).symm

end Transport

section ThetaShiftProofs

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLie GlobalTheory.FormalPoint
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {A : Type} [CommRing A]
  [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)

abbrev scaleE {R : Type} [CommRing R] (r : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR r)) (LieCombBaseChange.epsScale_over _)

theorem scaleE_cstE {A : Type} [CommRing A] (r : A) :
    (scaleE (PowerSeries.C (R := A) r)).left ≫ cstE A = cstE A ≫ (scaleE r).left := by
  refine (spMap_comp' _ _).trans (Eq.trans (congrArg spMap ?_) (spMap_comp' _ _).symm)
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

variable (hG : GlobalFnsSt)
include hG

theorem lieImg_scale {ν ν' : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (r : A)
    (P : GtPt.IsPull (scaleE r).left ν ν') : LieImg W ν' (scaleE (PowerSeries.C (R := A) r) ≫ v) := by
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨g', hg'⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have Q := Tr.cancel W.spec.1 W.e.surjective hg (tr_comp hg' (scaleE r) P) (scaleE (PowerSeries.C (R := A) r))
    (scaleE_cstE r)
  exact lieImg_of_tr W hg' (hp.pull _ Q)

theorem lieImg_act {ν ν' : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (x : 𝓞 E)
    (hν' : letI := H.starRing; IsSmulPt a.oa x ν ν') : LieImg W ν' (v ≫ W.t.act.act x) := by
  letI := H.starRing
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨g', hg'⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have s := Tr.smul hG W.spec.1 W.spec.2.1 W.e.surjective W.P.oD a.oa (fun x y => W.e.map_smul x y)
    W.spec.2.2.2.1 x (LieCombBaseChange.dualMap_over _) hg hg' hν'
  exact lieImg_of_tr W hg' (hp.smul hG W.P.lin x s)

end ThetaShiftProofs

theorem isEigGt_iff : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), LieImg W ν v → ((letI := H.starRing; GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsEigGt a.oa t ν) ↔ ∀ x : 𝓞 E, (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ v.left) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W t ν v hv
  letI := H.starRing
  refine forall_congr' fun x => ⟨fun ⟨ν', h₁, h₂⟩ => ?_, fun h => ?_⟩
  · have e := (ConstLie.main hG E H Dw l Xo c O β Y A b a χ W ν').1.unique (lieImg_act W hG hv x h₂)
      (lieImg_scale W hG hv (t x) h₁)
    exact congrArg (fun q => q.left) e
  · obtain ⟨ν', h₂⟩ := TorusModel.exists_isSmulPt hG a.oa x ν
    obtain ⟨ν'', h₁⟩ := ConstLie.exists_isPull (scaleE (t x)) ν
    obtain rfl : ν' = ν'' := ConstLie.eq_of_red W hG (lieImg_act W hG hv x h₂) (lieImg_scale W hG hv (t x) h₁)
      (congrArg (ConstLie.redE A ≫ ·) h)
    exact ⟨ν', h₁, h₂⟩

end GlobalTheory.ConstEig
