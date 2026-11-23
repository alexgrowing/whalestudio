import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LieArcSt
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LieLiftsTangentReduction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

noncomputable section

namespace GlobalTheory.ArcLieCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

section General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem prod_Oφ_zero {T : Over (Sp R)} (b : T ⟶ D.P.A) {Z : Scheme.{0}} (π : Z ⟶ T.left) (σ : Z ⟶ Sp R)
    (hb : π ≫ b.left = σ ≫ eSec D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (Z ⟶ D.P.A.left) → U) :
    ∏ k, h (π ≫ D.Oφ b χ k) ^ Oinvε k = 1 := by
  have hσ : σ = π ≫ T.hom := by
    have e : eSec D.P.A ≫ D.P.A.hom = 𝟙 (Sp R) := Over.w η[D.P.A]
    rw [← Over.w b, ← Category.assoc, hb, Category.assoc]
    exact ((congrArg (σ ≫ ·) e).trans (Category.comp_id _)).symm
  let FinalForm : Over (Sp R) := Over.mk (π ≫ T.hom)
  let π' : FinalForm ⟶ T := Over.homMk π rfl
  have h1 : π' ≫ b = 1 := Over.OverMorphism.ext (hb.trans (by
    rw [hσ]
    show _ = (toUnit FinalForm ≫ η[D.P.A]).left
    simp [eSec, FinalForm]))
  have e : ∀ k, π ≫ D.Oφ b χ k = D.Oφ (1 : FinalForm ⟶ D.P.A) χ k := fun k =>
    (WeightPf.Oφ_comp π' b χ k).trans (by rw [h1])
  simp only [e]
  rw [Fin.prod_univ_four]
  show h ((1 : FinalForm ⟶ D.P.A) * (toUnit FinalForm ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit FinalForm ≫ D.c χ).left ^ (1 : ℤ) *
    h (1 : FinalForm ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : FinalForm ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  simp

theorem exists_isZero (T : Over (Sp R)) : ∃ g : GtPt D T, g.IsZero := by
  have hF : ∀ χ, FormEq (PEmpty.elim : PEmpty → (T.left ⟶ D.P.A.left)) PEmpty.elim
      (DegPre.gtφT D T 1 χ) DegPre.gtε := fun χ U _ h => by
    have := prod_Oφ_zero (D := D) (1 : T ⟶ D.P.A) (𝟙 _) T.hom (by
      show 𝟙 _ ≫ (toUnit T ≫ η[D.P.A]).left = _
      simp [eSec]) χ h
    simp only [Category.id_comp] at this
    rw [TorusCoord.gtφT_eq]
    exact (Fintype.prod_empty _).trans this.symm
  choose s hs vs using fun χ => exists_gen D.P.isLB (hF χ) (LB.oneGen D.P.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  have v1 : ∀ χ y J, Good D.P.L y J → val (s χ) (𝟙 _) y J = 1 := fun χ y J hJ =>
    (vs χ _ _ y J hJ).trans (val_one _)
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => vs 0 _ _ y J hJ,
    fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl,
    fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩
  have c := val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1
  rw [MonObj.comp_one, (isCub_cubV D.cub hJ).face₃] at c
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v1 _ y J hJ) c)).trans
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v1 _ y J hJ) (v1 _ y J hJ))).symm

theorem exists_zero_pull_iff (ν : GtPt D (epsR R)) :
    (∃ g₀ : GtPt D (Over.mk (𝟙 (Sp R))), g₀.IsZero ∧ GtPt.IsPull (epsRed R) ν g₀) ↔ IsGtTangent ν := by
  have hz : (DegPre.zeroT D (Over.mk (𝟙 (Sp R)))).left = eSec D.P.A := by
    simp [eSec]
  constructor
  · rintro ⟨g₀, h₀, hp⟩
    refine ⟨hp.1.symm.trans (by rw [h₀.1]; exact hz), fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    exact (val_corr hJ (hp.2 χ) _).symm.trans (val_corr hJ (h₀.2 χ) _)
  · intro h
    obtain ⟨g₀, h₀⟩ := exists_isZero (D := D) (Over.mk (𝟙 (Sp R)))
    refine ⟨g₀, h₀, Eq.trans (by rw [h₀.1]; exact hz) h.1.symm, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    exact (val_corr hJ (h₀.2 χ) _).trans (val_corr hJ (h.2 χ) _).symm

omit [IsDomain R] in

theorem eSec_fstG (I : Ideal R) (e : ℕ) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] :
    eSec (thickObj R I e G) ≫ (fstG I e G).left = thick R I e ≫ eSec G :=
  (cubeMapOf (isGrpPullback_pullback G (thick R I e))).e_comm

variable {I : Ideal R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem eSec_pG : eSec (thickObj R I e G) ≫ g.pG.left = thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (·.left) (IsMonHom.one_hom g.q)
  rw [← eSec_fstG I e D.P.A, ← h, Category.assoc]
  rfl

theorem eq_eSec (x : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left)
    (hx : x ≫ g.pG.left = thick R I e ≫ eSec D.P.A)
    (ht : ∀ χ z J, Good D.P.L z J → val (g.t χ) x z J = 1) : x = eSec (thickObj R I e G) :=
  TorusCoord.ext_of_val g x _ (hx.trans (eSec_pG g).symm) fun χ z J hJ => by
    have h := (val_corr hJ (g.t_unit χ) (𝟙 _)).trans (val_one _)
    rw [val_pull hJ, Category.id_comp] at h
    exact (ht χ z J hJ).trans h.symm

theorem val_eq_one_of_genRelR {A : Type} [CommRing A] [IsLocalRing A] {B B₀ Z : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K]
    {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Sp A ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (h : GenRelR w t t₀) (r : Z ⟶ Sp A) (z : Z)
    (hz : ∀ f : (Z ⟶ B) → (Z.presheaf.stalk z)ˣ, ∏ k, f (r ≫ pt k) ^ ε k = 1)
    (h₀ : ∀ J, Good M₀ z J → val t₀ r z J = 1) {J'} (hJ' : Good M z J') : val t r z J' = 1 := by
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hM₀ z
  have v₁ := CubTransport.val_pmaps (fun k => (h.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR ((isGen_iff w).1 hw) hM hM₀ ht ht₀ h) r hJ hJ'
  rw [Category.comp_id, h₀ J hJ, hz (fun q => gw w q z (J (q ≫ φ)) (J' q)), _root_.one_mul] at v₁
  exact v₁.symm

omit [IsDomain R] in

theorem epsRed_dualMapR {R' : Type} [CommRing R'] (f : R →+* R') :
    epsRed R' ≫ spMap (dualMapR f) = spMap f ≫ epsRed R := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun x => ConstTan.fst_dualMapR _ x)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C) :
    spMap (f'.comp f) = spMap f' ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

omit [IsDomain R] in
theorem epsRed_hom : epsRed R ≫ (epsR R).hom = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
    RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
  rw [h3]
  exact Spec.map_id _

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section ThetaShiftProofs

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁}
  {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

theorem gtTan_iff (ν : GtPt a.D₀ (epsR K₁)) : GtTan (a := a) ν ↔ IsGtTangent ν :=
  exists_zero_pull_iff ν

theorem isTangent_of_isLieImage
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    {ν : GtPt a.D₀ (epsR K₁)} (hν : IsGtTangent ν) {v : epsR (PowerSeries K₁) ⟶ W.t.G} (hv : IsLieImage W ν v) :
    IsTangent v := by
  let I : Ideal (PowerSeries K₁) := Ideal.span {PowerSeries.X}
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_isUnit
  have : IsAdicComplete I (PowerSeries K₁) := inferInstance
  refine hom_ext_of_isHausdorff I fun e => ?_
  have : IsLocalRing (PowerSeries K₁ ⧸ I ^ (e + 1)) := isLocalRing_quotient_pow hI e
  have := ConstTan.isLocalRing_dual (PowerSeries K₁ ⧸ I ^ (e + 1))
  let m : PowerSeries K₁ →+* PowerSeries K₁ ⧸ I ^ (e + 1) := Ideal.Quotient.mk _
  let κ := dualMapR (m.comp (PowerSeries.C (R := K₁)))
  let s := (epsR (PowerSeries K₁ ⧸ I ^ (e + 1))).hom
  let r := epsRed (PowerSeries K₁ ⧸ I ^ (e + 1))
  have hs : s ≫ thick (PowerSeries K₁) I e = spMap (dualMapR m) ≫ (epsR (PowerSeries K₁)).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => (ConstTan.dualMapR_inl m r).symm)
  let xe : Sp (DualNumber (PowerSeries K₁ ⧸ I ^ (e + 1))) ⟶ (thickObj (PowerSeries K₁) I e W.t.G).left :=
    pullback.lift (spMap (dualMapR m) ≫ v.left) s (by rw [Category.assoc, Over.w v, hs])
  have hx : xe ≫ (fstG I e W.t.G).left = spMap (dualMapR m) ≫ v.left := pullback.lift_fst _ _ _
  have hx' : xe ≫ (thickObj (PowerSeries K₁) I e W.t.G).hom = s := pullback.lift_snd _ _ _
  have h' := hv e (dualMapR m) κ xe (ConstTan.dualMapR_inl _) (ConstTan.dualMapR_eps _)
    (ConstTan.dualMapR_inl _) (ConstTan.dualMapR_eps _) hx' hx
  have hκ : r ≫ spMap κ = (thick (PowerSeries K₁) I e ≫ spMap (PowerSeries.C (R := K₁))) ≫ epsRed K₁ :=
    (epsRed_dualMapR (m.comp (PowerSeries.C (R := K₁)))).trans (congrArg (· ≫ epsRed K₁) (spMap_comp (PowerSeries.C (R := K₁)) m))
  have hp : (r ≫ xe) ≫ (W.P.U.gt e).pG.left = thick (PowerSeries K₁) I e ≫ eSec W.P.D.toPre.P.A := by
    refine W.spec.1.1.hom_ext ?_ ?_
    · have h2 : (xe ≫ (W.P.U.gt e).pG.left) ≫ W.φ = spMap κ ≫ ν.b.left := (h' 0).1 2
      have h3 := congrArg (r ≫ ·) h2
      simp only [← Category.assoc] at h3
      refine h3.trans ((congrArg (· ≫ ν.b.left) hκ).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hν.1).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) W.he.symm).trans (Category.assoc _ _ _).symm)))))
    · have e₁ : eSec W.P.D.toPre.P.A ≫ W.P.D.toPre.P.A.hom = 𝟙 _ := Over.w η[W.P.D.toPre.P.A]
      have e₂ : (W.P.U.gt e).pG.left ≫ W.P.D.toPre.P.A.hom =
          (thickObj (PowerSeries K₁) I e W.t.G).hom ≫ thick (PowerSeries K₁) I e := Over.w _
      have e₃ : r ≫ s = 𝟙 _ := epsRed_hom
      refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans ?_)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans (Category.comp_id _))).symm
      rw [← Category.assoc, Category.assoc r, hx', e₃, Category.id_comp]
  have key : r ≫ xe = eSec (thickObj (PowerSeries K₁) I e W.t.G) := by
    refine eq_eSec (W.P.U.gt e) _ hp fun y z J' hJ' => ?_
    obtain ⟨x, rfl⟩ := W.e.surjective y
    refine (val_pull hJ' _ _ _).symm.trans (val_eq_one_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt e).t_gen _) xe) (DVR.pullGen_isGen _ _ _ _ (ν.isGen x) _) (h' x) r z
      (fun f => ?_) (fun J hJ => ?_) hJ')
    · refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (prod_Oφ_zero (W.P.U.gt e).pG (r ≫ xe) _ hp (W.e x) f)
      exact congrArg (fun q => f q ^ Oinvε k) (Category.assoc _ _ _).symm
    · exact (val_pull hJ _ _ _).trans ((congrArg (fun q => val (ν.s x) q z J) hκ).trans
        ((val_pull hJ _ _ _).symm.trans ((val_corr hJ (hν.2 x) _).trans (val_one _))))
  have h₁ : r ≫ spMap (dualMapR m) = thick (PowerSeries K₁) I e ≫ epsRed (PowerSeries K₁) := epsRed_dualMapR m
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ v.left) h₁.symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (r ≫ ·) hx.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) key).trans (eSec_fstG I e W.t.G))))))

theorem isLieImage_iff
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    {ν : GtPt a.D₀ (epsR K₁)} (hν : IsGtTangent ν) (v : epsR (PowerSeries K₁) ⟶ W.t.G) :
    IsLieImage W ν v ↔ IsTangent v ∧ IsLieImage W ν v :=
  ⟨fun h => ⟨isTangent_of_isLieImage W hν h, h⟩, fun h => h.2⟩

theorem lieLifts_iff
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ) :
    (∀ ν : GtPt a.D₀ (epsR K₁), GtTan (a := a) ν → ∃ v : epsR (PowerSeries K₁) ⟶ W.t.G, IsLieImage W ν v) ↔
      LieLifts W :=
  forall_congr' fun ν => ⟨fun h hν => (h ((gtTan_iff ν).2 hν)).imp fun v => (isLieImage_iff W hν v).1,
    fun h hν => (h ((gtTan_iff ν).1 hν)).imp fun _ => And.right⟩

end ThetaShiftProofs

theorem lieArcSt_iff {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    LieArcSt Y ↔ ∀ (K₁ : Type) [Field K₁] (b : O →+* K₁) (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
      (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ), LieLifts W :=
  ⟨fun h _ _ _ a χ W => (lieLifts_iff W).1 (h a χ W), fun h _ _ _ a χ W => (lieLifts_iff W).2 (h _ _ a χ W)⟩

variable (Xo c) in

theorem main : (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), LieArcSt Y) ↔ ArcLieLift Xo c :=
  ⟨fun h O _ β Y => (lieArcSt_iff Y).1 (h O β Y), fun h O _ β Y => (lieArcSt_iff Y).2 (h O β Y)⟩

end GlobalTheory.ArcLieCompare
