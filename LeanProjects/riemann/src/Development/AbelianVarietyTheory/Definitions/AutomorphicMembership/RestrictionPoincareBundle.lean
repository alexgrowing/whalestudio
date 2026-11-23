import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (thick thickObj thickMap thickTrans)
open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf (hMap sE)
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor GlobalTheory.Vert GlobalTheory.FormalPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

section Classes

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def IsRigCls (c : SmallPic G.left) : Prop := smallPull (eSec G) c = 0

def IsSymCls (c : SmallPic G.left) : Prop := smallPull (GrpObj.inv (X := G)).left c = c

def IsPrincipalCls (c : SmallPic G.left) : Prop :=
  ∃ (L : LB G.left) (hL : L.IsLB), smallCls L hL = c ∧ Out.RelAmple G L ∧ Out.KTriv G L

def RigPic : Type := {c : SmallPic G.left // IsRigCls G c}

variable {G}

omit [GrpObj G] [IsCommMonObj G] in

theorem smallCls_eq_zero_iff {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : smallCls L hL = 0 ↔ ∃ t : LB.Gen L, t.IsGen :=
  (smallPicEquiv X).symm.map_eq_zero_iff.trans (cls_eq_zero_iff hL)

omit [GrpObj G] [IsCommMonObj G] in

theorem smallPull_comp {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (c : SmallPic X) :
    smallPull (g ≫ f) c = smallPull g (smallPull f c) := by
  simp [smallPull, pull_comp]

omit [IsCommMonObj G] in

theorem isRigCls_iff {L : LB G.left} (hL : L.IsLB) : IsRigCls G (smallCls L hL) ↔ Out.Rigidified G L := by
  rw [IsRigCls, smallPull_smallCls _ hL (pull_isLB hL _), smallCls_eq_zero_iff]; rfl

def rigCls (L : RigLB G) : RigPic G := ⟨smallCls L.L L.isLB, (isRigCls_iff L.isLB).2 ⟨L.rig, L.rigGen⟩⟩

def IsBiextCls (P : RigPic (G ⊗ G)) : Prop := ∃ L : RigLB (G ⊗ G), rigCls L = P ∧ Nonempty (IsBiext G L.L)

def diagCls (w : G ⟶ G) (P : RigPic (G ⊗ G)) : SmallPic G.left := smallPull (lift (𝟙 G) w).left P.1

theorem isRigCls_diagCls (w : G ⟶ G) [IsMonHom w] (P : RigPic (G ⊗ G)) : IsRigCls G (diagCls w P) := by
  have e : η[G] ≫ lift (𝟙 G) w = η[G ⊗ G] := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [IsRigCls, diagCls, ← smallPull_comp, eSec, ← Over.comp_left, e]
  exact P.2

variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)

def sqMap : (G' ⊗ G').left ⟶ (G ⊗ G).left := (lift (pushHom h _ (fst G' G')) (pushHom h _ (snd G' G'))).left

omit [IsCommMonObj G] [IsCommMonObj G'] in

@[reassoc] theorem sqMap_fst : sqMap h ≫ (fst G G).left = (fst G' G').left ≫ φ :=
  congrArg (fun q => q.left) (lift_fst (pushHom h _ (fst G' G')) (pushHom h _ (snd G' G')))

omit [IsCommMonObj G] [IsCommMonObj G'] in

@[reassoc] theorem sqMap_snd : sqMap h ≫ (snd G G).left = (snd G' G').left ≫ φ :=
  congrArg (fun q => q.left) (lift_snd (pushHom h _ (fst G' G')) (pushHom h _ (snd G' G')))

omit [GrpObj G] [IsCommMonObj G] in

theorem sq_hom_ext {T : Scheme.{0}} {a b : T ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := pullback.hom_ext h₁ h₂

theorem eSec_sqMap : eSec (G' ⊗ G') ≫ sqMap h = f ≫ eSec (G ⊗ G) := by
  have e : η[G'].left ≫ φ = f ≫ η[G].left := (cubeMapOf h).e_comm
  refine sq_hom_ext ?_ ?_
  · rw [Category.assoc, sqMap_fst, eSec, eSec, ← Over.comp_left_assoc, Category.assoc, ← Over.comp_left,
      IsMonHom.one_hom, IsMonHom.one_hom, e]
  · rw [Category.assoc, sqMap_snd, eSec, eSec, ← Over.comp_left_assoc, Category.assoc, ← Over.comp_left,
      IsMonHom.one_hom, IsMonHom.one_hom, e]

def sqPull (P : RigPic (G ⊗ G)) : RigPic (G' ⊗ G') :=
  ⟨smallPull (sqMap h) P.1, by
    rw [IsRigCls, ← smallPull_comp, eSec_sqMap]
    exact (smallPull_comp _ _ _).trans ((congrArg _ P.2).trans (map_zero _))⟩

theorem smallPull_diagCls {w : G ⟶ G} {w' : G' ⟶ G'} (hw : w'.left ≫ φ = φ ≫ w.left) (P : RigPic (G ⊗ G)) :
    smallPull φ (diagCls w P) = diagCls w' (sqPull h P) := by
  refine (smallPull_comp _ _ _).symm.trans (Eq.trans (congrArg (smallPull · P.1) ?_) (smallPull_comp _ _ _))
  refine sq_hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, sqMap_fst, ← Over.comp_left, ← Over.comp_left_assoc, lift_fst, lift_fst]
    simp
  · rw [Category.assoc, Category.assoc, sqMap_snd, ← Over.comp_left, ← Over.comp_left_assoc, lift_snd, lift_snd, hw]

end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace tens

variable {X X' : Scheme.{0}} (t : SAB H X) (Λ : Unim E)

def ppCls : SmallPic (tens t Λ).G.left := smallCls (tens t Λ).PP.L (tens t Λ).PP.isLB

def poiCls : RigPic ((tens t Λ).G ⊗ (tens t Λ).G) := rigCls (poi t Λ)

def diag (P : RigPic ((tens t Λ).G ⊗ (tens t Λ).G)) : SmallPic (tens t Λ).G.left := diagCls ((tens t Λ).act.act H.w0) P

theorem diag_poiCls : diag t Λ (poiCls t Λ) = ppCls t Λ :=
  (smallPull_smallCls _ _ (pull_isLB (poi t Λ).isLB _)).trans ((smallCls_eq_iff _ _).2 (pp_iso_pull t Λ).symm)

variable {t} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)

theorem smallPull_diag (P : RigPic ((tens t Λ).G ⊗ (tens t Λ).G)) :
    smallPull (map Λ m).φ (diag t Λ P) = diag t' Λ (sqPull (map Λ m).cart P) :=
  smallPull_diagCls _ ((map Λ m).act H.w0) P

end tens

section MapRight

variable {S S' : Scheme.{0}} {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
  {G G' A A' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj A] [IsCommMonObj A]
  [GrpObj A'] [IsCommMonObj A'] {G₁ G₁' A₁ A₁' : Over S'} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₁'] [IsCommMonObj G₁']
  [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₁'] [IsCommMonObj A₁']
  {a : OAct O G} {a' : OAct O G'} {b : OAct O A} {b' : OAct O A'} {a₁ : OAct O G₁} {a₁' : OAct O G₁'} {b₁ : OAct O A₁}
  {b₁' : OAct O A₁'}

theorem mapRight_comm (t : IsTensor A b G a M) (t' : IsTensor A' b' G' a' M) (t₁ : IsTensor A₁ b₁ G₁ a₁ M)
    (t₁' : IsTensor A₁' b₁' G₁' a₁' M) {f : S' ⟶ S} {φ : G₁.left ⟶ G.left} {φ' : G₁'.left ⟶ G'.left} {ψ : A₁.left ⟶ A.left}
    {ψ' : A₁'.left ⟶ A'.left} (hψ : IsGrpPullback A₁ A f ψ) (hψ' : IsGrpPullback A₁' A' f ψ')
    (hm : ∀ m, (t₁.tmul m).left ≫ ψ = φ ≫ (t.tmul m).left) (hm' : ∀ m, (t₁'.tmul m).left ≫ ψ' = φ' ≫ (t'.tmul m).left)
    {q : G ⟶ G'} (hq : IsLinearHom a a' q) {q₁ : G₁ ⟶ G₁'} (hq₁ : IsLinearHom a₁ a₁' q₁) (e : q₁.left ≫ φ' = φ ≫ q.left) :
    (t₁.mapRight t₁' hq₁).left ≫ ψ' = ψ ≫ (t.mapRight t' hq).left := by
  have key : ∀ y : A₁ ⟶ A₁, pushHom hψ' A₁ (y ≫ t₁.mapRight t₁' hq₁) = pushHom hψ A₁ y ≫ t.mapRight t' hq := fun y => by
    refine t₁.induction_on (P := fun y => pushHom hψ' A₁ (y ≫ t₁.mapRight t₁' hq₁) =
      pushHom hψ A₁ y ≫ t.mapRight t' hq) y (by simp) (fun m x => Over.OverMorphism.ext ?_)
      (fun y z hy hz => by rw [MonObj.mul_comp, map_mul, map_mul, MonObj.mul_comp, hy, hz])
    rw [Category.assoc, IsTensor.tmul_mapRight]
    change (x.left ≫ _ ≫ _) ≫ ψ' = ((x.left ≫ _) ≫ ψ) ≫ _
    simp only [Category.assoc]
    rw [hm', reassoc_of% e, reassoc_of% hm, ← Over.comp_left _ _ _ (t.tmul m), IsTensor.tmul_mapRight, Over.comp_left]
  have e := congrArg (fun q => q.left) (key (𝟙 A₁))
  rw [Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp ψ))

end MapRight

section Thick

variable {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)

@[reassoc] theorem thickMap_fst (G : Over (Sp R)) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc] theorem thickMap_snd (G : Over (Sp R)) :
    thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) = pullback.snd G.hom (thick R I e) ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_thickMap (G : Over (Sp R)) [GrpObj G] :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (Out.thickTrans_comp R I e).symm (thickMap_fst I e G).symm)
    (thickMap_snd I e G)

theorem map_thickMap {G G' : Over (Sp R)} (u : G ⟶ G') :
    ((Over.pullback (thick R I e)).map u).left ≫ thickMap R I e G' =
      thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map u).left := by
  have h₁ : ∀ e, ((Over.pullback (thick R I e)).map u).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u.left :=
    fun _ => pullback.lift_fst _ _ _
  have h₂ : ∀ e, ((Over.pullback (thick R I e)).map u).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
    fun _ => pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, thickMap_fst, h₁, Category.assoc, h₁, thickMap_fst_assoc]
  · rw [Category.assoc, thickMap_snd, reassoc_of% h₂, Category.assoc, h₂, thickMap_snd]

end Thick

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (U : PELUnif I t) (Λ : Unim E)

def abPartAct : OAct (𝓞 E) U.D.toPre.P.A := letI := H.starRing; ofRingAct U.oD.onB.toRingAct

abbrev abTens : Over (Sp R) := Λ.obj (abPartAct U)

def abPartLB : RigLB U.D.toPre.P.A := ⟨U.D.toPre.P.L, U.D.toPre.rig, U.D.toPre.P.isLB, U.D.toPre.rig_gen⟩

def abTensLB : RigLB (abTens U Λ) := Λ.thetaOn (abPartAct U) H.w0 (abPartLB U)

theorem isLinearHom_q (e : ℕ) : IsLinearHom (t.act.pullback (thick R I e) _) ((abPartAct U).pullback (thick R I e) _)
    (U.U.gt e).q :=
  letI := H.starRing
  ⟨(U.U.gt e).q_hom, fun c => U.lin.q_lin e c⟩

def qTens (e : ℕ) : thickObj R I e (tens t Λ).G ⟶ thickObj R I e (abTens U Λ) :=
  ((tens.isTensor t Λ).pullback (thick R I e)).mapRight ((Λ.isTensor (abPartAct U)).pullback (thick R I e))
    (isLinearHom_q U e)

theorem isLinearHom_qTens (e : ℕ) : IsLinearHom ((tens t Λ).act.pullback (thick R I e) _)
    ((Λ.act (abPartAct U)).pullback (thick R I e) _) (qTens U Λ e) := IsTensor.isLinearHom_mapRight _ _ _

theorem q_thickMap (e : ℕ) : (U.U.gt e).q.left ≫ thickMap R I e _ = thickMap R I e _ ≫ (U.U.gt (e + 1)).q.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, thickMap_fst, Category.assoc]
    exact (U.U.gt_q e).symm
  · have h₁ : (U.U.gt e).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.U.gt e).q
    have h₂ : (U.U.gt (e + 1)).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.U.gt (e + 1)).q
    rw [Category.assoc, thickMap_snd, reassoc_of% h₁, Category.assoc, h₂, thickMap_snd]

theorem qTens_thickMap (e : ℕ) : (qTens U Λ e).left ≫ thickMap R I e _ = thickMap R I e _ ≫ (qTens U Λ (e + 1)).left :=
  mapRight_comm ((tens.isTensor t Λ).pullback (thick R I (e + 1))) ((Λ.isTensor (abPartAct U)).pullback (thick R I (e + 1)))
    ((tens.isTensor t Λ).pullback (thick R I e)) ((Λ.isTensor (abPartAct U)).pullback (thick R I e))
    (isGrpPullback_thickMap I e (tens t Λ).G) (isGrpPullback_thickMap I e (abTens U Λ))
    (fun m => by rw [IsTensor.pullback_tmul, IsTensor.pullback_tmul]; exact map_thickMap I e _)
    (fun m => by rw [IsTensor.pullback_tmul, IsTensor.pullback_tmul]; exact map_thickMap I e _)
    (isLinearHom_q U (e + 1)) (isLinearHom_q U e) (q_thickMap U e)

end Unif

section Point

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) (Λ : Unim E)

def defIdeal : Ideal ↥(intO ↥C.S) := (maximalIdeal A.R).map A.f

abbrev gPt : Over (Sp ↥(intO ↥C.S)) := (Over.pullback (spMap A.f)).obj (tens A.t Λ).G

abbrev bPt : Over (Sp ↥(intO ↥C.S)) := (Over.pullback (spMap A.f)).obj (abTens A.U Λ)

def gPtIsTensor : IsTensor (gPt A Λ) ((tens A.t Λ).act.pullback (spMap A.f) _) ((Over.pullback (spMap A.f)).obj A.t.G)
    (A.t.act.pullback (spMap A.f) _) Λ.L := (tens.isTensor A.t Λ).pullback _

def bPtIsTensor : IsTensor (bPt A Λ) ((Λ.act (abPartAct A.U)).pullback (spMap A.f) _)
    ((Over.pullback (spMap A.f)).obj A.U.D.toPre.P.A) ((abPartAct A.U).pullback (spMap A.f) _) Λ.L :=
  (Λ.isTensor (abPartAct A.U)).pullback _

abbrev gtLev (e : ℕ) : Over (Sp (↥(intO ↥C.S) ⧸ defIdeal A ^ (e + 1))) := thickObj _ (defIdeal A) e (gPt A Λ)

abbrev bLev (e : ℕ) : Over (Sp (↥(intO ↥C.S) ⧸ defIdeal A ^ (e + 1))) := thickObj _ (defIdeal A) e (bPt A Λ)

abbrev gtTrans (e : ℕ) : (gtLev A Λ e).left ⟶ (gtLev A Λ (e + 1)).left := thickMap _ (defIdeal A) e (gPt A Λ)

def levToDat (G : Over (Sp A.R)) (e : ℕ) : (thickObj _ (defIdeal A) e ((Over.pullback (spMap A.f)).obj G)).left ⟶
    (thickObj A.R (maximalIdeal A.R) e G).left := hMap (φ := A.f) (hφ := le_rfl) G _ (𝟙 _)

theorem isGrpPullback_levToDat (G : Over (Sp A.R)) [GrpObj G] (e : ℕ) :
    IsGrpPullback (thickObj _ (defIdeal A) e ((Over.pullback (spMap A.f)).obj G)) (thickObj A.R (maximalIdeal A.R) e G)
      (sE A.f le_rfl e) (levToDat A G e) :=
  @Out.PullGtPf.isGrpPullback_hMap _ _ _ _ _ _ _ _ A.f le_rfl e G _ _ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _)))

@[reassoc] theorem levToDat_fst (G : Over (Sp A.R)) (e : ℕ) :
    levToDat A G e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst G.hom (spMap A.f) :=
  (Out.PullGtPf.hMap_fst _ _ _).trans (congrArg _ (Category.id_comp _))

def prLev (e : ℕ) : gtLev A Λ e ⟶ bLev A Λ e :=
  Over.homMk ((isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift (levToDat A _ e ≫ (qTens A.U Λ e).left) (gtLev A Λ e).hom
    (by rw [Category.assoc, Over.w]; exact (isGrpPullback_levToDat A _ e).1.w))
    ((isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift_snd _ _ _)

@[reassoc] theorem prLev_levToDat (e : ℕ) :
    (prLev A Λ e).left ≫ levToDat A _ e = levToDat A _ e ≫ (qTens A.U Λ e).left :=
  (isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift_fst _ _ _

instance isMonHom_prLev (e : ℕ) : IsMonHom (prLev A Λ e) :=
  have := (isLinearHom_qTens A.U Λ e).1
  Out.PullGtPf.isMonHom_of_grpPullback (isGrpPullback_levToDat A _ e) (isGrpPullback_levToDat A _ e) (qTens A.U Λ e) _
    (prLev_levToDat A Λ e)

def prPt (e : ℕ) : (gtLev A Λ e).left ⟶ (bPt A Λ).left := (prLev A Λ e).left ≫ pullback.fst _ _

theorem prPt_fst (e : ℕ) : prPt A Λ e ≫ pullback.fst _ _ = levToDat A _ e ≫ (qTens A.U Λ e).left ≫ pullback.fst _ _ := by
  rw [prPt, Category.assoc, ← levToDat_fst, prLev_levToDat_assoc]

theorem prPt_hom (e : ℕ) : prPt A Λ e ≫ (bPt A Λ).hom = pullback.fst _ _ ≫ (gPt A Λ).hom := by
  have h : (prLev A Λ e).left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (prLev A Λ e)
  rw [prPt, Category.assoc, pullback.condition, pullback.condition, reassoc_of% h]

theorem gtTrans_prPt (e : ℕ) : gtTrans A Λ e ≫ prPt A Λ (e + 1) = prPt A Λ e := by
  apply pullback.hom_ext
  · have h : gtTrans A Λ e ≫ levToDat A _ (e + 1) = levToDat A _ e ≫ thickMap _ _ e _ := Out.PullGtPf.hMap_thick _ _ _
    rw [Category.assoc, prPt_fst, prPt_fst, reassoc_of% h, ← reassoc_of% qTens_thickMap, thickMap_fst]
  · exact (Category.assoc _ _ _).trans ((congrArg _ (prPt_hom A Λ (e + 1))).trans
      ((thickMap_fst_assoc _ _ _ _).trans (prPt_hom A Λ e).symm))

abbrev GtPic : Type := FPic (X := fun e => (gtLev A Λ e).left) (gtTrans A Λ)

def prPullPt (M : SmallPic (bPt A Λ).left) : GtPic A Λ := fpull (prPt A Λ) (gtTrans_prPt A Λ) M

def completePt (L : SmallPic (gPt A Λ).left) : GtPic A Λ :=
  fpull (fun _ => pullback.fst _ _) (fun e => thickMap_fst _ e _) L

def mmPt : SmallPic (bPt A Λ).left :=
  smallPull (pullback.fst (abTens A.U Λ).hom (spMap A.f)) (smallCls _ (abTensLB A.U Λ).isLB)

variable {X : Scheme.{0}} {π : X ⟶ Y.X} {t : SAB H X} (m : SABMap t Y.t π) (z : Sp ↥(intO ↥C.S) ⟶ X) (hz : z ≫ π = P.yt)

include hz in

theorem isGrpPullback_gPt_base : IsGrpPullback (gPt A Λ) (tens Y.t Λ).G (z ≫ π) (pullback.fst _ _ ≫ (tens.map Λ A.m).φ) :=
  ((isGrpPullback_pullback _ (spMap A.f)).comp (tens.map Λ A.m).cart).congr (A.fac.trans hz.symm) rfl

def gPtTo : (gPt A Λ).left ⟶ (tens t Λ).G.left :=
  (tens.map Λ m).cart.1.lift (pullback.fst _ _ ≫ (tens.map Λ A.m).φ) ((gPt A Λ).hom ≫ z)
    (by rw [(isGrpPullback_gPt_base A Λ z hz).1.w, Category.assoc])

theorem gPtTo_φ : gPtTo A Λ m z hz ≫ (tens.map Λ m).φ = pullback.fst _ _ ≫ (tens.map Λ A.m).φ :=
  (tens.map Λ m).cart.1.lift_fst _ _ _

end Point

section Generic

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p} (Z : Mdl Y i₀)

def Mdl.tQ : SAB H Z.genO.toScheme := (Geo.Tor.exists_sab Z.genO.ι Z.t).choose

def Mdl.tQMap : SABMap Z.tQ Z.t Z.genO.ι := (Geo.Tor.exists_sab Z.genO.ι Z.t).choose_spec.some

end Generic

section Record

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def thbTrue (ct : At S κ p) : ThbSt ct (uniTrue ct) where
  LBG Λ := SmallPic (tens ct.Xm.t Λ).G.left
  LBGq Λ := SmallPic (tens ct.Xm.tQ Λ).G.left
  resQ {Λ} := smallPull (tens.map Λ ct.Xm.tQMap).φ
  PPq Λ := tens.ppCls ct.Xm.tQ Λ
  symmG := IsSymCls _
  rigG := IsRigCls _
  LBGt y Λ := GtPic (ct.dat y) Λ
  LBB y Λ := SmallPic (bPt (ct.dat y) Λ).left
  resGt {Λ} L y := completePt (ct.dat y) Λ (smallPull (gPtTo (ct.dat y) Λ ct.Xm.tMap y.z y.z_π) L)
  prPull {y Λ} := prPullPt (ct.dat y) Λ
  principal := IsPrincipalCls _
  StrictHenselianAcyclic Λ := RigPic ((tens ct.Xm.t Λ).G ⊗ (tens ct.Xm.t Λ).G)
  squareRootLineBundle Λ := RigPic ((tens ct.Xm.tQ Λ).G ⊗ (tens ct.Xm.tQ Λ).G)
  res2 {Λ} := sqPull (tens.map Λ ct.Xm.tQMap).cart
  PoiQ Λ := tens.poiCls ct.Xm.tQ Λ
  biext := IsBiextCls
  dg {Λ} := tens.diag ct.Xm.t Λ
  dgq {Λ} := tens.diag ct.Xm.tQ Λ
  dg_res {Λ} P := tens.smallPull_diag Λ ct.Xm.tQMap P
  PPq_def Λ := (tens.diag_poiCls ct.Xm.tQ Λ).symm

variable (ct : At S κ p) (Λ : (uniTrue ct).Unim)

example (P : (thbTrue ct).StrictHenselianAcyclic Λ) : (thbTrue ct).dg P = diagCls ((tens ct.Xm.t Λ).act.act (BoundaryLocalData.w0 D)) P := by
  rw [← amb_w0_eq_boundaryLocalData_w0 A]; rfl

example (P : (thbTrue ct).StrictHenselianAcyclic Λ) : (thbTrue ct).rigG ((thbTrue ct).dg P) :=
  haveI := (tens ct.Xm.t Λ).act.hom A.H.w0
  isRigCls_diagCls _ P

example (y : ct.Pt ct.Xm) (L : (thbTrue ct).LBG Λ) (M : (thbTrue ct).LBB y Λ)
    (h : (thbTrue ct).resGt L y = (thbTrue ct).prPull M) (e : ℕ) :
    smallPull (pullback.fst _ _) (smallPull (gPtTo (ct.dat y) Λ ct.Xm.tMap y.z y.z_π) L) =
      smallPull (prPt (ct.dat y) Λ e) M :=
  (level_fpull _ _ e _).symm.trans ((congrArg (level e) h).trans (level_fpull _ _ e _))

end Record

end GlobalTheory.LocM
