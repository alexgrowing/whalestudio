import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransported
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ConstLie

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open GlobalTheory.ConstTan GlobalTheory.FormalPoint

section General

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}

theorem exists_isPullGt (ρ : T' ⟶ T) (g : GtPt D T) : ∃ g' : GtPt D T', GtPt.IsPull ρ.left g g' := by
  choose s hs vs using fun χ => exists_gen D.P.isLB (φ' := DegPre.gtφT D T' (ρ ≫ g.b) χ) (ε' := DegPre.gtε)
    (fun U _ f => Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
      (ConstTanRed.comp_gtφT D ρ g.b _ rfl χ k)) (LB.pullGen D.P.L _ _ (g.s χ) ρ.left)
    (pullGen_isGen _ _ _ _ (g.isGen χ) _)
  have vs' : ∀ χ y J, Good D.P.L y J → val (s χ) (𝟙 _) y J = val (g.s χ) ρ.left y J := fun χ y J hJ => by
    rw [vs χ _ _ y J hJ, val_pull hJ, Category.id_comp]
  refine ⟨⟨ρ ≫ g.b, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩,
    rfl, fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩
  · exact (vs' 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans ((val_one _).trans (val_one _).symm))
  · have e := val_s_add g ρ (z := y) hJ χ χ'
    have c := val_cub D.cub (𝟙 T') hJ (cP D T' χ) (cP D T' χ') (ρ ≫ g.b)
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at c
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) (vs' _ y J hJ) c) (e.trans ?_))
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs' _ y J hJ) (vs' _ y J hJ))).symm

def ZeroAlong (g : GtPt D T) (ρ : T' ⟶ T) : Prop :=
  ρ ≫ g.b = 1 ∧ ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J, Good D.P.L z J → val (g.s χ) (r ≫ ρ.left) z J = 1

theorem isZero_iff_zeroAlong {ρ : T' ⟶ T} {g : GtPt D T} {g' : GtPt D T'} (h : GtPt.IsPull ρ.left g g') :
    g'.IsZero ↔ ZeroAlong g ρ := by
  have hb : g'.b = ρ ≫ g.b := Over.OverMorphism.ext h.1
  refine and_congr (by rw [hb]; rfl) (forall_congr' fun χ => ⟨fun H Z r z J hJ => ?_, fun H => ?_⟩)
  · exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) r).symm.trans ((val_corr hJ H r).trans (val_one _)))
  · exact corr_of_val D.P.isLB fun y J hJ => (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans
      ((H _ _ y J hJ).trans (val_one _).symm))

end General

section Base

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} [IsHausdorff I R] {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}

theorem isZero_iff_eq_one {g : GtPt D.toPre (Over.mk (𝟙 (Sp R)))} {x : Over.mk (𝟙 (Sp R)) ⟶ G}
    (hx : IsPointOf U g x) : g.IsZero ↔ x = 1 := by
  constructor
  · intro h
    refine Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e => ?_)
    have w : (thick R I e ≫ x.left) ≫ G.hom = 𝟙 _ ≫ thick R I e := by
      rw [Category.assoc, Over.w x, Category.id_comp]; exact Category.comp_id _
    have hy : pullback.lift _ _ w ≫ (fstG I e G).left = thick R I e ≫ x.left := pullback.lift_fst _ _ _
    exact hy.symm.trans ((isPointOf_one U h).comp_fstG_eq (hx e _ _ _ hy))
  · rintro rfl
    rw [isPointOf_iff] at hx
    have H : ∀ e, thick R I e ≫ g.b.left = thick R I e ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ D.toPre.P.A).left ∧
        ∀ χ z J, Good D.toPre.P.L z J → val (g.s χ) (thick R I e) z J = 1 := fun e => by
      let Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (𝟙 _)
      let r : (Over.map (thick R I e)).obj Z ⟶ Over.mk (𝟙 (Sp R)) :=
        Over.homMk (thick R I e) ((Category.comp_id _).trans (Category.id_comp _).symm)
      have h1 : (Over.map (thick R I e)).map (1 : Z ⟶ thickObj R I e G) ≫ fstG I e G = 1 := by
        have := map_mul_fstG (1 : Z ⟶ thickObj R I e G) 1
        rw [_root_.mul_one] at this
        exact mul_eq_left.1 this.symm
      obtain ⟨h₁, h₂⟩ := hx e Z r 1 (h1.trans (MonObj.comp_one r).symm)
      rw [TorusCoord.im_one] at h₁
      exact ⟨congrArg (fun q => q.left) (h₁.symm.trans (MonObj.comp_one r).symm), fun χ z J hJ =>
        (h₂ χ z J hJ).symm.trans (TorusCoord.val_unit (U.gt e) χ (Z := Z) (z := z) hJ)⟩
    have hb : g.b = 1 := Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e => (H e).1)
    refine ⟨hb, fun χ => CompletePoint.corr_of_thick I D.toPre.P.isLB (fun V _ f => ?_) (g.isGen χ)
      (fun _ _ => (map_one _).trans
        ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
      fun e z J hJ => ((H e).2 χ z J hJ).trans (val_one _).symm⟩
    have p := prod_gtφT (𝟙 _) g.b χ f
    simp only [Over.id_left, Category.id_comp] at p
    refine p.trans ?_
    rw [hb, _root_.mul_one]
    simp

end Base

section Through

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left} (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (e : D.X → D'.X)
  {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left)

def Through (g₀ : GtPt D T) (g : GtPt D' T') : Prop :=
  ∀ x, (∀ k, DegPre.gtφT D' T' g.b (e x) k ≫ Φ = h ≫ DegPre.gtφT D T g₀.b x k) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (g₀.s x) (r ≫ h) z J =
        (∏ k, ConstFam.wVal w z J J' (r ≫ DegPre.gtφT D' T' g.b (e x) k) ^ DegPre.gtε k) * val (g.s (e x)) r z J'

variable {w e h}

theorem Through.zeroAlong_iff {f : Sp R' ⟶ Sp R} (gp : IsPullback Φ D'.P.A.hom D.P.A.hom f)
    (he : Function.Surjective e) {g₀ : GtPt D T} {g : GtPt D' T'} (H : Through w e h g₀ g)
    {S : Over (Sp R)} {S' : Over (Sp R')} (ρ : S ⟶ T) (ρ' : S' ⟶ T') (c : S'.left ⟶ S.left)
    (hc : ρ'.left ≫ h = c ≫ ρ.left) (σ : S.left ⟶ S'.left) (hσ : σ ≫ c = 𝟙 _) :
    ZeroAlong g₀ ρ ↔ ZeroAlong g ρ' := by
  have b₁ : (ρ' ≫ g.b).left ≫ Φ = c ≫ (ρ ≫ g₀.b).left := by
    have : g.b.left ≫ Φ = h ≫ g₀.b.left := (H 0).1 2
    rw [Over.comp_left, Over.comp_left, Category.assoc, this, reassoc_of% hc]
  have b₂ : (1 : S' ⟶ D'.P.A).left ≫ Φ = c ≫ (1 : S ⟶ D.P.A).left := by
    have : (1 : T' ⟶ D'.P.A).left ≫ Φ = h ≫ (1 : T ⟶ D.P.A).left := (H 0).1 3
    rw [← MonObj.comp_one ρ, ← MonObj.comp_one ρ', Over.comp_left, Over.comp_left, Category.assoc, this,
      reassoc_of% hc]
  have hv : ρ' ≫ g.b = 1 → ∀ x (Z : Scheme.{0}) (r : Z ⟶ S'.left) (z : Z) J J', Good D.P.L z J →
      Good D'.P.L z J' → val (g₀.s x) ((r ≫ c) ≫ ρ.left) z J = val (g.s (e x)) (r ≫ ρ'.left) z J' := by
    intro hb x Z r z J J' hJ hJ'
    have v := (H x).2 Z (r ≫ ρ'.left) z J J' hJ hJ'
    have p := prod_gtφT ρ' g.b (e x) (fun q => ConstFam.wVal w z J J' (r ≫ q))
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel] at p
    simp only [Category.assoc] at v ⊢
    rw [p, _root_.one_mul, hc] at v
    exact v
  constructor
  · rintro ⟨h₁, h₂⟩
    have hb : ρ' ≫ g.b = 1 := Over.OverMorphism.ext (gp.hom_ext (by rw [b₁, b₂, h₁])
      ((Over.w _).trans (Over.w _).symm))
    refine ⟨hb, fun y Z r z J' hJ' => ?_⟩
    obtain ⟨x, rfl⟩ := he y
    obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.P.isLB z
    exact (hv hb x Z r z J J' hJ hJ').symm.trans (h₂ x Z _ z J hJ)
  · rintro ⟨h₁, h₂⟩
    refine ⟨Over.OverMorphism.ext ?_, fun x Z r z J hJ => ?_⟩
    · rw [h₁, b₂] at b₁
      have := congrArg (σ ≫ ·) b₁
      simp only [reassoc_of% hσ] at this
      exact this.symm
    · obtain ⟨J', hJ'⟩ := ConstFam.exists_good' D'.P.isLB z
      have v := hv h₁ x Z (r ≫ σ) z J J' hJ hJ'
      rw [Category.assoc r, hσ, Category.comp_id] at v
      exact v.trans (h₂ _ Z _ z J' hJ')

theorem Through.genRelR {A : Type} [CommRing A] [IsLocalRing A] (hw : w.IsGen) {g₀ : GtPt D T} {g : GtPt D' T'}
    (H : Through w e h g₀ g) (r : Sp A ⟶ T'.left) (x : D.X) {pt : Fin 4 → (Sp A ⟶ D'.P.A.left)}
    {t : LB.Gen (LB.LinComb D'.P.L pt DegPre.gtε)} (ht : t.IsGen)
    (hp : ∀ k, pt k = r ≫ DegPre.gtφT D' T' g.b (e x) k)
    (hv : ∀ J, Good D'.P.L (cpt A) J → val t (𝟙 _) (cpt A) J = val (g.s (e x)) r (cpt A) J) :
    GenRelR w t (LB.pullGen _ _ _ (g₀.s x) (r ≫ h)) := by
  refine ConstPoint.genRelR_of_val hw D'.P.isLB D.P.isLB ht (pullGen_isGen _ _ _ _ (g₀.isGen x) _)
    (fun k => by rw [hp, Category.assoc, (H x).1, Category.assoc]) fun J J' hJ hJ' => ?_
  rw [val_pull hJ, Category.id_comp, hv J' hJ']
  simp only [Category.id_comp, hp]
  exact (H x).2 _ r _ J J' hJ hJ'

end Through

section ThetaShiftProofs

open PowerSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {χ : Sp A⟦X⟧ ⟶ Y.X} {W : Wit Y a χ} {ν : Out.GtPt a.D₀ (epsR A)} {g : Out.GtPt W.P.D.toPre (epsR A⟦X⟧)}

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

omit [IsDomain A] in
theorem span_X_ne_top : Ideal.span {(X : A⟦X⟧)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top, PowerSeries.isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

theorem lieImg_of_isPointOf (hT : Through W.w W.e (spMap (dualMapR (C (R := A)))) ν g) {v : epsR A⟦X⟧ ⟶ W.t.G}
    (hv : IsPointOf W.P.U.toUnifPre g v) : LieImg W ν v := by
  intro n ρ κ vn h₁ h₂ h₃ h₄ _ h₆ x
  have := isLocalRing_quotient_pow (span_X_ne_top (A := A)) n
  have := isLocalRing_dual (A⟦X⟧ ⧸ Ideal.span {(X : A⟦X⟧)} ^ (n + 1))
  have hκ : κ = ρ.comp (dualMapR (C (R := A))) :=
    (eq_dualMapR ((Ideal.Quotient.mk _).comp C) κ h₃ h₄).trans (eq_dualMapR _ _
      (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (h₁ _)) ((congrArg ρ (dualMapR_eps _)).trans h₂)).symm
  obtain ⟨k₁, k₂⟩ := (hasCoords_iff _ _ _ _ _).1 (hv n _ (spMap ρ) vn h₆)
  rw [hκ, ← spMap_comp']
  exact hT.genRelR W.spec.2.1 (spMap ρ) x (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt n).t_gen _) vn)
    (fun k => ((TorusCoord.comp_eq_of_left g.b (W.P.U.gt n).pG (spMap ρ) vn k₁.symm).1 _ k).symm)
    fun J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun q => val _ q _ J) (Category.id_comp vn)).trans (k₂ _ _ J hJ))

theorem eq_of_lieImg [IsHausdorff ((Ideal.span {(X : A⟦X⟧)}).map (algebraMap A⟦X⟧ (DualNumber A⟦X⟧)))
      (DualNumber A⟦X⟧)] (hT : Through W.w W.e (spMap (dualMapR (C (R := A)))) ν g) {v v' : epsR A⟦X⟧ ⟶ W.t.G}
    (hv : IsPointOf W.P.U.toUnifPre g v) (hD : LieImg W ν v') : v' = v := by
  have := isLocalRing_dual A⟦X⟧
  let I : Ideal A⟦X⟧ := Ideal.span {X}
  refine Over.OverMorphism.ext (hom_ext_of_isHausdorff (I.map (algebraMap A⟦X⟧ (DualNumber A⟦X⟧))) fun e => ?_)
  have : IsLocalRing (A⟦X⟧ ⧸ I ^ (e + 1)) := isLocalRing_quotient_pow (span_X_ne_top (A := A)) e
  have := isLocalRing_dual (A⟦X⟧ ⧸ I ^ (e + 1))
  let ρ : DualNumber A⟦X⟧ →+* DualNumber (A⟦X⟧ ⧸ I ^ (e + 1)) := dualMapR (Ideal.Quotient.mk _)
  let s : Sp (DualNumber (A⟦X⟧ ⧸ I ^ (e + 1))) ⟶ Sp (A⟦X⟧ ⧸ I ^ (e + 1)) := spMap (algebraMap _ _)
  have hs : s ≫ Out.thick A⟦X⟧ I e = spMap ρ ≫ (epsR A⟦X⟧).hom :=
    (spMap_comp' _ _).trans ((congrArg spMap
      (RingHom.ext fun r => (dualMapR_inl (Ideal.Quotient.mk (I ^ (e + 1))) r).symm)).trans (spMap_comp' _ _).symm)
  let xe : Sp (DualNumber (A⟦X⟧ ⧸ I ^ (e + 1))) ⟶ (Out.thickObj A⟦X⟧ I e W.t.G).left :=
    pullback.lift (spMap ρ ≫ v'.left) s (by rw [Category.assoc, Over.w v', hs])
  have hx : xe ≫ (Out.fstG I e W.t.G).left = spMap ρ ≫ v'.left := pullback.lift_fst _ _ _
  have hx' : xe ≫ ((Over.map (Out.thick A⟦X⟧ I e)).obj (Out.thickObj A⟦X⟧ I e W.t.G)).hom =
      spMap ρ ≫ (epsR A⟦X⟧).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans hs)
  have hκ := spMap_comp' (dualMapR (C (R := A))) ρ
  have h' := hD e ρ (ρ.comp (dualMapR (C (R := A)))) xe (dualMapR_inl _) (dualMapR_eps _)
    (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (dualMapR_inl _ _))
    ((congrArg ρ (dualMapR_eps _)).trans (dualMapR_eps _)) (pullback.lift_snd _ _ _) hx
  have hb : xe ≫ (W.P.U.gt e).pG.left = spMap ρ ≫ g.b.left := by
    refine W.spec.1.1.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans (((Category.assoc _ _ _).symm.trans ((h' 0).1 2)).trans ?_)
      exact (congrArg (· ≫ _) hκ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap ρ ≫ ·) ((hT 0).1 2).symm).trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, Category.assoc, Over.w, Over.w]
      exact hx'
  have hg : ∀ x, GenRelR W.w (g.s (W.e x)) (LB.pullGen _ _ _ (ν.s x) (𝟙 _ ≫ spMap (dualMapR (C (R := A))))) :=
    fun x => hT.genRelR W.spec.2.1 (𝟙 _) x (g.isGen _) (fun k => (Category.id_comp _).symm) fun _ _ => rfl
  have hC : HasCoords W.P.U.toUnifPre e g (spMap ρ) xe := ⟨hb, fun y => by
    obtain ⟨x, rfl⟩ := W.e.surjective y
    exact ConstTanFormal.corr_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB (g.isGen _)
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt e).t_gen _) xe) (ν.isGen x)
      ((congrArg (spMap ρ ≫ ·) (Category.id_comp _)).trans hκ)
      (fun k => ((TorusCoord.comp_eq_of_left g.b (W.P.U.gt e).pG (spMap ρ) xe hb.symm).1 _ k).symm) (hg x) (h' x)⟩
  have key : spMap ρ ≫ v'.left = spMap ρ ≫ v.left := hx.symm.trans (hv.comp_fstG_eq hC)
  have hk : RingHom.ker ρ ≤ RingHom.ker (Ideal.Quotient.mk (I.map (algebraMap A⟦X⟧ (DualNumber A⟦X⟧)) ^ (e + 1))) := by
    rw [Ideal.mk_ker, ← Ideal.map_pow]
    exact ConstTanFormal.ker_dualMapR_mk _
  have hρ : Function.Surjective ρ := ConstTanFormal.dualMapR_surjective Ideal.Quotient.mk_surjective
  have hl := ρ.liftOfSurjective_comp hρ ⟨_, hk⟩
  have e₁ : adicLevelι (I.map (algebraMap A⟦X⟧ (DualNumber A⟦X⟧))) (e + 1) =
      spMap (ρ.liftOfSurjective hρ ⟨_, hk⟩) ≫ spMap ρ := by
    rw [spMap_comp', hl]
  rw [e₁, Category.assoc, Category.assoc, key]

end ThetaShiftProofs

theorem main : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR A)), (∃! v : epsR (PowerSeries A) ⟶ W.t.G, LieImg W ν v) ∧ ∀ v, LieImg W ν v → (GtTanR ν ↔ IsTangent v) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ν
  have := isLocalRing_dual (PowerSeries A)
  have : Module.Finite (PowerSeries A) (DualNumber (PowerSeries A)) :=
    inferInstanceAs (Module.Finite (PowerSeries A) (PowerSeries A × PowerSeries A))
  have := isAdicComplete_map_of_finite (Ideal.span {(PowerSeries.X : PowerSeries A)}) (DualNumber (PowerSeries A))
  obtain ⟨gp, hw, -, -, hc, -⟩ := W.spec
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp hw W.e.symm.toAddEquiv.toAddMonoidHom
    (fun y => by have := hc (W.e.symm y); rwa [LinearEquiv.apply_symm_apply] at this)
    (T := epsR A) (T' := epsR (PowerSeries A)) (spMap (dualMapR (PowerSeries.C (R := A))))
    ((spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => dualMapR_inl _ r)).trans (spMap_comp' _ _).symm)) ν
  have hT : Through W.w W.e (spMap (dualMapR (PowerSeries.C (R := A)))) ν g := fun x => by
    have := hg (W.e x)
    have e : W.e.symm.toAddEquiv.toAddMonoidHom (W.e x) = x := W.e.symm_apply_apply x
    rw [e] at this
    exact this
  obtain ⟨v, hv, -⟩ := existsUnique_isPointOf W.P.U.toUnifPre g
  refine ⟨⟨v, lieImg_of_isPointOf hT hv, fun v' h => eq_of_lieImg hT hv h⟩, fun v' h => ?_⟩
  obtain rfl := eq_of_lieImg hT hv h
  have sec : ∀ (R : Type) [CommRing R], spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsR R).hom = 𝟙 (Sp R) :=
    fun R _ => (spMap_comp' _ _).trans (Spec.map_id _)
  let p₀ : Over.mk (𝟙 (Sp A)) ⟶ epsR A := Over.homMk _ (sec A)
  let p : Over.mk (𝟙 (Sp (PowerSeries A))) ⟶ epsR (PowerSeries A) := Over.homMk _ (sec _)
  obtain ⟨g₀, h₀⟩ := exists_isPullGt p₀ ν
  obtain ⟨g₁, h₁⟩ := exists_isPullGt p g
  have e₁ : GtTanR ν ↔ ZeroAlong ν p₀ :=
    ⟨fun ⟨_, hz, hp⟩ => (isZero_iff_zeroAlong (ρ := p₀) hp).1 hz, fun hz => ⟨g₀, (isZero_iff_zeroAlong h₀).2 hz, h₀⟩⟩
  have e₂ : ZeroAlong ν p₀ ↔ ZeroAlong g p :=
    hT.zeroAlong_iff gp.1 W.e.surjective p₀ p (spMap (PowerSeries.C (R := A)))
      ((spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => fst_dualMapR _ r)).trans (spMap_comp' _ _).symm))
      (spMap (PowerSeries.constantCoeff (R := A)))
      ((spMap_comp' _ _).trans ((congrArg spMap PowerSeries.constantCoeff_comp_C).trans (Spec.map_id _)))
  have e₃ : p ≫ v' = 1 ↔ IsTangent v' := by
    have o : (1 : Over.mk (𝟙 (Sp (PowerSeries A))) ⟶ W.t.G).left = η[W.t.G].left := Category.id_comp _
    exact ⟨fun h => (congrArg (fun q : Over.mk (𝟙 (Sp (PowerSeries A))) ⟶ W.t.G => q.left) h).trans o, fun h => Over.OverMorphism.ext (h.trans o.symm)⟩
  exact e₁.trans (e₂.trans ((isZero_iff_zeroAlong h₁).symm.trans ((isZero_iff_eq_one (hv.pull p h₁)).trans e₃)))

end GlobalTheory.ConstLie
