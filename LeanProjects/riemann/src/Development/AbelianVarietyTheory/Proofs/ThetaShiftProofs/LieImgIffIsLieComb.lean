import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransported
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOrigin

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstLin
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}

def Thru (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (e : D'.X → D.X) {T : Over (Sp R)} {T' : Over (Sp R')}
    (h : T'.left ⟶ T.left) (g₀ : GtPt D T) (g : GtPt D' T') : Prop :=
  ∀ y, (∀ k, DegPre.gtφT D' T' g.b y k ≫ Φ = h ≫ DegPre.gtφT D T g₀.b (e y) k) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (g₀.s (e y)) (r ≫ h) z J =
        (∏ k, ConstFam.wVal w z J J' (r ≫ DegPre.gtφT D' T' g.b y k) ^ DegPre.gtε k) * val (g.s y) r z J'

variable (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) {w : LB.Iso D'.P.L (D.P.L.pull Φ)} {e : D'.X → D.X}
  {T : Over (Sp R)} {T' : Over (Sp R')} {h : T'.left ⟶ T.left}

theorem Thru.val_id {g₀ : GtPt D T} {g : GtPt D' T'} (H : Thru w e h g₀ g) (y) (z : T'.left) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') : val (g₀.s (e y)) h z J =
      (ConstFam.wVal w z J J' (cP D' T' y * g.b).left)⁻¹ * ConstFam.wVal w z J J' (cP D' T' y).left *
        ConstFam.wVal w z J J' g.b.left * (ConstFam.wVal w z J J' (1 : T' ⟶ D'.P.A).left)⁻¹ *
        val (g.s y) (𝟙 _) z J' := by
  have v := (H y).2 _ (𝟙 _) z J J' hJ hJ'
  have p := FormalPoint.prod_gtφT (𝟙 T') g.b y (ConstFam.wVal w z J J')
  rw [Category.id_comp] at v p
  exact v.trans (congrArg (· * _) p)

include gp in
theorem Thru.isZero {g₀ : GtPt D T} {g : GtPt D' T'} (H : Thru w e h g₀ g) (h₀ : g₀.IsZero) : g.IsZero := by
  have hb : g.b = (1 : T' ⟶ D'.P.A) := Over.OverMorphism.ext (gp.1.hom_ext
    (((H 0).1 2).trans ((congrArg (fun q => h ≫ q.left) h₀.1).trans ((H 0).1 3).symm))
    ((Over.w _).trans (Over.w _).symm))
  refine ⟨hb, fun y => corr_of_val D'.P.isLB fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.P.isLB z
  have v := H.val_id y z hJ hJ'
  rw [(val_corr hJ (h₀.2 (e y)) h).trans (val_one _)] at v
  rw [val_one]
  generalize val (g.s y) (𝟙 _) z J' = s at v ⊢
  rw [hb, _root_.mul_one] at v
  simpa using v.symm

include gp in
theorem Thru.isPull {T₁ : Over (Sp R)} {T₁' : Over (Sp R')} {h₁ : T₁'.left ⟶ T₁.left} {g₀ : GtPt D T} {g : GtPt D' T'}
    {g₀₁ : GtPt D T₁} {g₁ : GtPt D' T₁'} (H : Thru w e h g₀ g) (H₁ : Thru w e h₁ g₀₁ g₁) (k : T₁' ⟶ T')
    {k₀ : T₁.left ⟶ T.left} (hk : k.left ≫ h = h₁ ≫ k₀) (h₀ : GtPt.IsPull k₀ g₀ g₀₁) :
    GtPt.IsPull k.left g g₁ := by
  have hb : k ≫ g.b = g₁.b := Over.OverMorphism.ext (gp.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (k.left ≫ ·) ((H 0).1 2)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g₀.b.left) hk).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₁ ≫ ·) h₀.1.symm).trans ((H₁ 0).1 2).symm))))))
    ((Over.w _).trans (Over.w _).symm))
  refine ⟨congrArg (fun q => q.left) hb.symm, fun y => corr_of_val D'.P.isLB fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.P.isLB z
  have v := (H y).2 _ k.left z J J' hJ hJ'
  have v₁ := (H₁ y).2 _ (𝟙 _) z J J' hJ hJ'
  have c := (val_corr hJ (h₀.2 (e y)) h₁).trans (val_pull hJ _ _ _)
  simp only [ConstTanRed.comp_gtφT D' k g.b g₁.b hb] at v
  simp only [Category.id_comp] at v₁
  rw [val_pull hJ', Category.id_comp]
  rw [hk] at v
  exact mul_left_cancel (v₁.symm.trans (c.trans v))

include gp in
theorem Thru.isAdd (hG : GlobalFnsSt) (hw : w.IsGen) (hh : h ≫ T.hom = T'.hom ≫ spMap f)
    {g₀ g₀' g₀'' : GtPt D T} {g g' g'' : GtPt D' T'} (r : Thru w e h g₀ g) (r' : Thru w e h g₀' g')
    (r'' : Thru w e h g₀'' g'') (h₀ : g₀.IsAdd g₀' g₀'') : g.IsAdd g' g'' := by
  let ρ : Over.mk (T'.hom ≫ spMap f) ⟶ T := Over.homMk h hh
  have b : pushHom gp T' g.b = ρ ≫ g₀.b := Over.OverMorphism.ext ((r 0).1 2)
  have b' : pushHom gp T' g'.b = ρ ≫ g₀'.b := Over.OverMorphism.ext ((r' 0).1 2)
  have b'' : pushHom gp T' g''.b = ρ ≫ g₀''.b := Over.OverMorphism.ext ((r'' 0).1 2)
  have hb : g''.b = g.b * g'.b := ConstGrp.push_injective gp T' (by
    rw [map_mul, b, b', b'', h₀.1]; exact MonObj.comp_mul _ _ _)
  refine ⟨hb, fun y => corr_of_val D'.P.isLB fun z J' hJ' => ?_⟩
  have hc : pushHom gp T' (cP D' T' y) = ρ ≫ cP D T (e y) := Over.OverMorphism.ext ((r y).1 1)
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.P.isLB z
  have a := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub ρ hJ _ _ _))).symm.trans
    ((val_corr hJ (h₀.2 (e y)) ρ.left).trans (val_mul hJ _ _ _))
  have c := ConstGrp.cubV_push gp hG D'.P.isAb D.cub D'.cub ((isGen_iff w).1 hw) (cP D' T' y) g.b g'.b hJ hJ'
    (ConstFam.wVal w z J J') (fun _ => rfl)
  rw [hc, b, b'] at c
  have a' := (congrArg₂ (fun p q : (T'.left.presheaf.stalk z)ˣ => p * q) (r''.val_id y z hJ hJ') c).symm.trans
    (a.trans (congrArg₂ (fun p q : (T'.left.presheaf.stalk z)ˣ => p * q) (r.val_id y z hJ hJ') (r'.val_id y z hJ hJ')))
  have v := val_cub D'.cub (𝟙 T') hJ' (cP D' T' y) g.b g'.b
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at v
  refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl v)).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  generalize val (g''.s y) (𝟙 _) z J' = s'' at a' ⊢
  rw [hb, ← _root_.mul_assoc (cP D' T' y)] at a'
  apply Additive.ofMul.injective
  have a'' := congrArg Additive.ofMul a'
  simp only [ofMul_mul, ofMul_inv] at a'' ⊢
  linear_combination (norm := abel) a''

end Thru

section Level

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D₀ : DegPre R}
  {I : Ideal R'} {D : DegData R' I} {A : PolAV (Spec (CommRingCat.of (FractionRing R')))}
  {G : Over (Spec (CommRingCat.of R'))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {Φ : D.toPre.P.A.left ⟶ D₀.P.A.left}

theorem comp_Oφ {D : DegPre R} {T T' T'' : Over (Sp R)} (x : T'' ⟶ T') (r : T'' ⟶ T) (p : T' ⟶ D.P.A) (b : T ⟶ D.P.A)
    (hb : x ≫ p = r ≫ b) (χ : D.X) (k : Fin 4) :
    x.left ≫ D.Oφ p χ k = r.left ≫ DegPre.gtφT D T b χ k := by
  rw [ConstTanRed.comp_gtφT D r b _ hb.symm]
  fin_cases k
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul x p (cP D T' χ)).trans
      ((congrArg ((x ≫ p) * ·) (comp_cP D x χ)).trans (_root_.mul_comm _ _)))
  · exact congrArg (fun q => q.left) (comp_cP D x χ)
  · rfl
  · exact congrArg (fun q : T'' ⟶ D.P.A => q.left) (MonObj.comp_one x)

theorem hasCoords_iff_genRelR (gp : IsGrpPullback D.toPre.P.A D₀.P.A (spMap f) Φ)
    {w : LB.Iso D.toPre.P.L (D₀.P.L.pull Φ)} (hw : w.IsGen) (e : D₀.X ≃ D.toPre.X)
    {T : Over (Sp R)} {T' : Over (Sp R')} {h : T'.left ⟶ T.left} {g₀ : GtPt D₀ T} {g : GtPt D.toPre T'}
    (H : Thru w e.symm h g₀ g) (n : ℕ) {S : Type} [CommRing S] [IsLocalRing S] (r : Sp S ⟶ T'.left)
    (y : Sp S ⟶ (thickObj R' I n G).left) (hy : y ≫ (fstG I n G).left ≫ G.hom = r ≫ T'.hom) :
    FormalPoint.HasCoords U n g r y ↔
      ∀ x, GenRelR w (LB.pullGen _ _ _ ((U.gt n).t (e x)) y) (LB.pullGen _ _ _ (g₀.s x) (r ≫ h)) := by
  have hy' : y ≫ ((Over.map (thick R' I n)).obj (thickObj R' I n G)).hom = r ≫ T'.hom := by
    rw [← hy, Over.w (fstG I n G)]
  let y' : Over.mk (r ≫ T'.hom) ⟶ (Over.map (thick R' I n)).obj (thickObj R' I n G) := Over.homMk y hy'
  let r' : Over.mk (r ≫ T'.hom) ⟶ T' := Over.homMk r rfl
  have key : y ≫ (U.gt n).pG.left = r ≫ g.b.left → ∀ χ k,
      y ≫ D.toPre.Oφ (U.gt n).pG χ k = r ≫ DegPre.gtφT D.toPre T' g.b χ k := fun hb =>
    comp_Oφ y' r' _ _ (Over.OverMorphism.ext hb)
  have eP : y ≫ (U.gt n).pG.left = r ≫ g.b.left → ∀ χ (z : Sp S) J J',
      ∏ k, ConstFam.wVal w z J J' (𝟙 _ ≫ y ≫ D.toPre.Oφ (U.gt n).pG χ k) ^ Oinvε k =
        ∏ k, ConstFam.wVal w z J J' (r ≫ DegPre.gtφT D.toPre T' g.b χ k) ^ DegPre.gtε k := fun hb χ z J J' =>
    Finset.prod_congr rfl fun k _ => congrArg (fun q => ConstFam.wVal w z J J' q ^ DegPre.gtε k)
      ((Category.id_comp _).trans (key hb χ k))
  rw [FormalPoint.hasCoords_iff]
  constructor
  · rintro ⟨hb, hv⟩ x
    obtain ⟨χ, rfl⟩ := e.symm.surjective x
    rw [Equiv.apply_symm_apply]
    refine ConstPoint.genRelR_of_val hw D.toPre.P.isLB D₀.P.isLB (pullGen_isGen _ _ _ _ ((U.gt n).t_gen _) y)
      (pullGen_isGen _ _ _ _ (g₀.isGen _) _) (fun k => ?_) fun J J' hJ hJ' => ?_
    · rw [key hb, Category.assoc, (H χ).1 k, Category.assoc]
    · have a₀ := val_pull hJ (g₀.s (e.symm χ)) (r ≫ h) (𝟙 _)
      have a₁ := val_pull hJ' ((U.gt n).t χ) y (𝟙 _)
      rw [Category.id_comp] at a₀ a₁
      exact a₀.trans (((H χ).2 _ r _ J J' hJ hJ').trans
        (congrArg₂ (· * ·) (eP hb χ _ J J').symm (a₁.trans (hv χ _ J' hJ')).symm))
  · intro h'
    have h'' : ∀ χ, GenRelR w (LB.pullGen _ _ _ ((U.gt n).t χ) y)
        (LB.pullGen _ _ _ (g₀.s (e.symm χ)) (r ≫ h)) := fun χ => by
      have := h' (e.symm χ)
      rwa [Equiv.apply_symm_apply] at this
    have hb : y ≫ (U.gt n).pG.left = r ≫ g.b.left := gp.1.hom_ext
      (((h'' 0).1 2).trans ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) ((H 0).1 2).symm).trans
        (Category.assoc _ _ _).symm)))
      (by rw [Category.assoc, Category.assoc, Over.w, Over.w]; exact hy')
    refine ⟨hb, fun χ z J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := ConstFam.exists_good' D₀.P.isLB z
    have P := ConstGrp.pmaps_of_genRelR ((isGen_iff w).1 hw) D.toPre.P.isLB D₀.P.isLB
      (pullGen_isGen _ _ _ _ ((U.gt n).t_gen _) y) (pullGen_isGen _ _ _ _ (g₀.isGen _) _) (h'' χ)
    have v := ConstFam.pmaps_val (fun k => ((h'' χ).1 k).trans (Category.id_comp _).symm) P (𝟙 _) hJ hJ'
    have a₀ := val_pull hJ (g₀.s (e.symm χ)) (r ≫ h) (𝟙 _ ≫ 𝟙 _)
    have a₁ := val_pull hJ' ((U.gt n).t χ) y (𝟙 _)
    rw [Category.id_comp y] at a₁
    have a₂ : (𝟙 _ ≫ 𝟙 _) ≫ r ≫ h = r ≫ h := by simp
    rw [a₂] at a₀
    exact mul_left_cancel ((congrArg₂ (· * ·) (eP hb χ _ J J') a₁).symm.trans
      (v.symm.trans (a₀.trans ((H χ).2 _ r _ J J' hJ hJ'))))

end Level

section ThetaShiftProofs

open GlobalTheory.ArcQ GlobalTheory.ConstTan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {A : Type} [CommRing A]
  [IsDomain A] [IsLocalRing A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}

def Reads (W : Wit Y a χ) (ν : GtPt a.D₀ (epsR A)) (g : GtPt W.P.D.toPre (epsR (PowerSeries A))) : Prop :=
  Thru W.w W.e.toEquiv.symm (T := epsR A) (T' := epsR (PowerSeries A)) (spMap (dualMapR (PowerSeries.C (R := A)))) ν g

omit [IsDomain A] [IsLocalRing A] in
theorem dualMapR_over {A' : Type} [CommRing A'] (f : A →+* A') :
    spMap (dualMapR f) ≫ (epsR A).hom = (epsR A').hom ≫ spMap f :=
  (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun r => dualMapR_inl _ r)).trans (spMap_comp _ _))

omit [IsLocalRing A] in
theorem exists_reads (hG : GlobalFnsSt) (W : Wit Y a χ) (ν : GtPt a.D₀ (epsR A)) : ∃ g, Reads W ν g := by
  obtain ⟨gp, hw, -, -, hc, -⟩ := W.spec
  exact ConstPoint.exists_gtPt_through hG gp hw W.e.symm.toAddEquiv.toAddMonoidHom
    (fun y => by have := hc (W.e.symm y); rwa [LinearEquiv.apply_symm_apply] at this)
    (T := epsR A) (T' := epsR (PowerSeries A)) _ (dualMapR_over _) ν

theorem lieImg_iff (W : Wit Y a χ) {ν : GtPt a.D₀ (epsR A)} {g : GtPt W.P.D.toPre (epsR (PowerSeries A))}
    (h : Reads W ν g) (v : epsR (PowerSeries A) ⟶ W.t.G) :
    LieImg W ν v ↔ FormalPoint.IsPointOf W.P.U.toUnifPre g v := by
  let I : Ideal (PowerSeries A) := Ideal.span {PowerSeries.X}
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_unit
  have loc : ∀ n, IsLocalRing (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) := fun n =>
    have : IsLocalRing (PowerSeries A ⧸ I ^ (n + 1)) := isLocalRing_quotient_pow hI n
    isLocalRing_dual _
  have hκ : ∀ n, spMap (dualMapR (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ spMap (dualMapR (PowerSeries.C (R := A))) =
      spMap ((dualMapR (Ideal.Quotient.mk (I ^ (n + 1)))).comp (dualMapR (PowerSeries.C (R := A)))) := fun n =>
    (Spec.map_comp _ _).symm
  constructor
  · intro hL
    refine (FormalPoint.isPointOf_iff_reduction _ g v).2 fun n => ?_
    have := loc n
    let ρ : DualNumber (PowerSeries A) →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) := dualMapR (Ideal.Quotient.mk _)
    let s : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ Sp (PowerSeries A ⧸ I ^ (n + 1)) := spMap (algebraMap _ _)
    have hs : s ≫ thick (PowerSeries A) I n = spMap ρ ≫ (epsR (PowerSeries A)).hom := (dualMapR_over _).symm
    let xe : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (thickObj (PowerSeries A) I n W.t.G).left :=
      pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs])
    have hx : xe ≫ (fstG I n W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
    have h' := hL n ρ (ρ.comp (dualMapR (PowerSeries.C (R := A)))) xe (dualMapR_inl _) (dualMapR_eps _)
      (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (dualMapR_inl _ _))
      ((congrArg ρ (dualMapR_eps _)).trans (dualMapR_eps _)) (pullback.lift_snd _ _ _) hx
    rw [← hκ n] at h'
    have hc := (hasCoords_iff_genRelR W.P.U.toUnifPre W.spec.1 W.spec.2.1 W.e.toEquiv h n (spMap ρ) xe
      (by rw [← Category.assoc, hx, Category.assoc, Over.w v])).2 h'
    let J : Ideal (DualNumber (PowerSeries A)) := I.map (algebraMap (PowerSeries A) (DualNumber (PowerSeries A)))
    have hk : RingHom.ker ρ ≤ RingHom.ker (Ideal.Quotient.mk (J ^ (n + 1))) := by
      rw [Ideal.mk_ker, ← Ideal.map_pow]
      exact ConstTanFormal.ker_dualMapR_mk _
    have hsurj : Function.Surjective ρ := ConstTanFormal.dualMapR_surjective Ideal.Quotient.mk_surjective
    let q := ρ.liftOfSurjective hsurj ⟨_, hk⟩
    have hq : spMap q ≫ spMap ρ = adicLevelι J (n + 1) :=
      (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.liftOfSurjective_comp ρ hsurj _))
    have hr : FormalPoint.reduction I v n = spMap q ≫ xe := by
      rw [← cancel_mono (fstG I n W.t.G).left, FormalPoint.reduction_fstG, Category.assoc, hx, ← Category.assoc, hq]
    have := hc.comp (spMap q)
    rw [hq, ← hr] at this
    exact this
  · intro hP n ρ κ vn h₁ h₂ h₃ h₄ _ h₆
    have := loc n
    obtain rfl := eq_dualMapR (Ideal.Quotient.mk (I ^ (n + 1))) ρ h₁ h₂
    obtain rfl : κ = (dualMapR (Ideal.Quotient.mk (I ^ (n + 1)))).comp (dualMapR (PowerSeries.C (R := A))) :=
      (eq_dualMapR ((Ideal.Quotient.mk (I ^ (n + 1))).comp (PowerSeries.C (R := A))) κ h₃ h₄).trans
        (eq_dualMapR _ _ (fun r => (congrArg _ (dualMapR_inl _ r)).trans (dualMapR_inl _ _))
          ((congrArg _ (dualMapR_eps _)).trans (dualMapR_eps _))).symm
    rw [← hκ n]
    exact (hasCoords_iff_genRelR W.P.U.toUnifPre W.spec.1 W.spec.2.1 W.e.toEquiv h n _ vn
      (by rw [← Category.assoc, h₆, Category.assoc, Over.w v])).1 (hP n _ _ vn h₆)

omit [IsDomain A] [IsLocalRing A] in

def scaleOver (c : A) : epsR A ⟶ epsR A := Over.homMk (spMap (epsScaleR c))
  ((spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun r => by
    ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])))

omit [IsDomain A] [IsLocalRing A] in
theorem scale_dualMapR {A' : Type} [CommRing A'] (f : A →+* A') (c : A) :
    spMap (epsScaleR (f c)) ≫ spMap (dualMapR f) = spMap (dualMapR f) ≫ spMap (epsScaleR c) :=
  (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun r => by
    ext <;> simp [dualMapR, epsScaleR, _root_.mul_comm])).trans (spMap_comp _ _))

theorem chain {M α : Type} [Monoid M] (P : α → M → Prop) : ∀ (m : ℕ) (p : Fin (m + 1) → α) (u : Fin m → M) (x : M),
    P (p 0) x → (∀ (i : Fin m) y, P (p i.castSucc) y → P (p i.succ) (y * u i)) →
    P (p (Fin.last m)) (x * (List.ofFn u).prod)
  | 0, p, u, x, h, _ => by simpa using h
  | m + 1, p, u, x, h, hs => by
    have := chain P m (fun i => p i.succ) (fun i => u i.succ) (x * u 0) (hs 0 x h) fun i y hy => hs i.succ y hy
    rw [List.ofFn_succ, List.prod_cons, ← _root_.mul_assoc]
    exact this

end ThetaShiftProofs

open Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames in

theorem lieImg_iff_isLieComb : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (m : ℕ) (cf : Fin m → A) (e : Fin m → Out.GtPt a.D₀ (epsR A)) (ν : Out.GtPt a.D₀ (epsR A)) (v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)) (w : epsR (PowerSeries A) ⟶ W.t.G), (∀ i, LieImg W (e i) (v i)) → GtComb cf e ν → (LieImg W ν w ↔ IsLieComb (fun i => PowerSeries.C (R := A) (cf i)) v w) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W m cf e ν v w hv ⟨u, p, hu, h₀, hp, hν⟩
  subst hν
  choose rd hrd using exists_reads hG W
  let u' : Fin m → (epsR (PowerSeries A) ⟶ W.t.G) := fun i => scaleOver (PowerSeries.C (cf i)) ≫ v i
  have hu' : ∀ i, FormalPoint.IsPointOf W.P.U.toUnifPre (rd (u i)) (u' i) := fun i =>
    ((lieImg_iff W (hrd _) _).1 (hv i)).pull _ (Thru.isPull W.spec.1 (hrd (e i)) (hrd (u i))
      (scaleOver (PowerSeries.C (cf i))) (scale_dualMapR _ _) (hu i))
  have hs := chain (fun q x => FormalPoint.IsPointOf W.P.U.toUnifPre (rd q) x) m p u' 1
    (FormalPoint.isPointOf_one _ (Thru.isZero W.spec.1 (hrd _) h₀)) fun i y hy =>
      hy.mul hG (hu' i) (Thru.isAdd W.spec.1 hG W.spec.2.1 (dualMapR_over _) (hrd _) (hrd _) (hrd _) (hp i))
  rw [_root_.one_mul] at hs
  rw [lieImg_iff W (hrd _)]
  have := ConstTan.isLocalRing_dual (PowerSeries A)
  have : Module.Finite (PowerSeries A) (DualNumber (PowerSeries A)) :=
    inferInstanceAs (Module.Finite (PowerSeries A) (PowerSeries A × PowerSeries A))
  have := isAdicComplete_map_of_finite (Ideal.span {(PowerSeries.X : PowerSeries A)}) (DualNumber (PowerSeries A))
  refine ⟨fun h => ⟨u', fun i => rfl, h.unique hs⟩, fun ⟨u'', h₁, h₂⟩ => ?_⟩
  obtain rfl : u'' = u' := funext fun i => Over.OverMorphism.ext (h₁ i)
  rw [h₂]
  exact hs

end GlobalTheory.ConstLin
