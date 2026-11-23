import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanAdd

section General

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem corr_mul {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (ρ : (Over.map (thick R I e)).obj T' ⟶ T) (x x' : T' ⟶ thickObj R I e G) (p p' p'' : GtPt D T)
    (h : GtPt.IsAdd p p' p'') (hb : TorusCoord.im g x = ρ ≫ p.b) (hb' : TorusCoord.im g x' = ρ ≫ p'.b) (χ : D.X)
    (hs : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x.left) (LB.pullGen D.P.L _ _ (p.s χ) ρ.left))
    (hs' : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x'.left) (LB.pullGen D.P.L _ _ (p'.s χ) ρ.left)) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (x * x').left) (LB.pullGen D.P.L _ _ (p''.s χ) ρ.left) := by
  refine corr_of_val D.P.isLB fun z J hJ => ?_
  have k := TorusCoord.val_t_mul_points g GlobalTheory.globalFns_holds χ x x' z J hJ
  have a := val_corr hJ (h.2 χ) ρ.left
  have a₁ := (val_mul hJ _ _ _).symm.trans (a.trans (val_mul hJ _ _ _))
  have c : val (DegPre.cubAtT D T (DegPre.cT D T χ) p.b p'.b) ρ.left z J = TorusCoord.cubeVal g χ z J x x' := by
    refine (val_cub D.cub ρ hJ _ _ _).trans ?_
    unfold TorusCoord.cubeVal
    rw [hb, hb']
    congr 1
    simp
  have s := ((val_pull hJ _ _ _).symm.trans (val_corr hJ hs (𝟙 _))).trans (val_pull hJ _ _ _)
  have s' := ((val_pull hJ _ _ _).symm.trans (val_corr hJ hs' (𝟙 _))).trans (val_pull hJ _ _ _)
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  simp only [Category.id_comp] at s s' ⊢
  refine mul_right_cancel (k.trans ?_)
  exact ((congrArg₂ (· * ·) s s').trans a₁.symm).trans (congrArg (_ * ·) c)

theorem fst_mul {T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T' ⟶ thickObj R I e G) :
    (Over.map (thick R I e)).map (x * x') ≫ fstG I e G =
      ((Over.map (thick R I e)).map x ≫ fstG I e G) * ((Over.map (thick R I e)).map x' ≫ fstG I e G) :=
  map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T') x x'

end General

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_over {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ (epsR A).hom = (epsR B).hom ≫ spMap f := by
  change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_scale {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c : A) :
    spMap (epsScaleR (f c)) ≫ spMap (dualMap f) = spMap (dualMap f) ≫ spMap (epsScaleR c) := by
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap, epsScaleR, mul_comm]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem tanRel_mul (y y' : epsR R ⟶ G) (gm gm' gm'' : GtPt D.toPre (epsR R)) (h : TanRel U y gm) (h' : TanRel U y' gm')
    (ha : GtPt.IsAdd gm gm' gm'') : TanRel U (y * y') gm'' := by
  intro e
  obtain ⟨ye, h₁, h₂, h₃⟩ := h e
  obtain ⟨ye', h₁', h₂', h₃'⟩ := h' e
  have hci : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hw := dual_over (Ideal.Quotient.mk (I ^ (e + 1)))
  let ρ : (Over.map (thick R I e)).obj (epsR (R ⧸ I ^ (e + 1))) ⟶ epsR R :=
    Over.homMk (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))) hw
  have key : ∀ (w : epsR R ⟶ G) (we : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left),
      we ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ w.left →
      we ≫ (thickObj R I e G).hom = (epsR (R ⧸ I ^ (e + 1))).hom := by
    intro w we hh
    have h0 := congrArg (· ≫ G.hom) hh
    simp only [Category.assoc, Over.w] at h0
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact h0.trans hw
  let x : epsR (R ⧸ I ^ (e + 1)) ⟶ thickObj R I e G := Over.homMk ye (key y ye h₁)
  let x' : epsR (R ⧸ I ^ (e + 1)) ⟶ thickObj R I e G := Over.homMk ye' (key y' ye' h₁')
  have f : (Over.map (thick R I e)).map x ≫ fstG I e G = ρ ≫ y := Over.OverMorphism.ext h₁
  have f' : (Over.map (thick R I e)).map x' ≫ fstG I e G = ρ ≫ y' := Over.OverMorphism.ext h₁'
  have b : TorusCoord.im (U.gt e) x = ρ ≫ gm.b := Over.OverMorphism.ext h₂
  have b' : TorusCoord.im (U.gt e) x' = ρ ≫ gm'.b := Over.OverMorphism.ext h₂'
  refine ⟨(x * x').left, ?_, ?_, fun χ => corr_mul (U.gt e) ρ x x' gm gm' gm'' ha b b' χ (h₃ χ) (h₃' χ)⟩
  · have := fst_mul x x'
    rw [f, f', ← MonObj.comp_mul] at this
    exact congrArg (·.left) this
  · have := TorusCoord.im_mul (U.gt e) x x'
    rw [b, b', ← MonObj.comp_mul] at this
    rw [ha.1]
    exact congrArg (·.left) this

theorem tanRel_scale (c : R) (y : epsR R ⟶ G) (gm gm' : GtPt D.toPre (epsR R)) (h : TanRel U y gm)
    (hp : GtPt.IsPull (epsScale R c).left gm gm') : TanRel U (epsScale R c ≫ y) gm' := by
  intro e
  obtain ⟨ye, h₁, h₂, h₃⟩ := h e
  have hc : spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c)) ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ (epsScale R c).left := dual_scale _ c
  refine ⟨spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c)) ≫ ye, ?_, ?_, fun χ => ?_⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans ?_)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.left) hc).trans (Category.assoc _ _ _))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ gm.b.left) hc).trans ((Category.assoc _ _ _).trans ?_))
    exact congrArg (_ ≫ ·) hp.1.symm
  · refine corr_of_val D.toPre.P.isLB fun z J hJ => ?_
    have s := ((val_pull hJ _ _ _).symm.trans
      (val_corr hJ (h₃ χ) (spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c))))).trans (val_pull hJ _ _ _)
    have t := (val_corr hJ (hp.2 χ) (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))))).trans (val_pull hJ _ _ _)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    simp only [Category.id_comp]
    exact s.trans ((congrArg (fun q => val (gm.s χ) q z J) hc).trans t.symm)

theorem main : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => (∀ (y y' : epsR V ⟶ G) (gm gm' gm'' : GtPt D.toPre (epsR V)), TanRel U.toUnifPre y gm → TanRel U.toUnifPre y' gm' → GtPt.IsAdd gm gm' gm'' → TanRel U.toUnifPre (y * y') gm'') ∧ ∀ (c : V) (y : epsR V ⟶ G) (gm gm' : GtPt D.toPre (epsR V)), TanRel U.toUnifPre y gm → GtPt.IsPull (epsScale V c).left gm gm' → TanRel U.toUnifPre (epsScale V c ≫ y) gm' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U => ⟨tanRel_mul U.toUnifPre, tanRel_scale U.toUnifPre⟩

end GlobalTheory.MBLow.TanAdd

end
