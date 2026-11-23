import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamValTauAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOriginOneOfGenericOriginDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericOriginOneTautologicalBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsMultiplicative
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EDiv

open GlobalTheory.TorusExt ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] gtGroup

section Action

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

theorem cPoint_act (oa : D.OAct O) (T : Over (Spec (CommRingCat.of R))) (a : O) (χ : D.X) :
    cP D T (a • χ) = cP D T χ ≫ oa.onB.act a := by
  rw [cP, oa.c_lin, ← Category.assoc]; rfl

theorem exists_ptRos (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) :
    ∃ u, IsRos D.P.L (oa.onB.act (star a)) (oa.onB.act a) u := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  rw [star_star] at hr
  exact exists_ros hG D.P.isAb D.P.isLB _ _ hr

def ptRos (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) := (exists_ptRos hG oa a).choose

theorem ptRos_isRos (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) :
    IsRos D.P.L (oa.onB.act (star a)) (oa.onB.act a) (ptRos hG oa a) := (exists_ptRos hG oa a).choose_spec

theorem ptAct_iff_val (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) (g g' : GtPtF D F) :
    GtPtAct oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      charVal g' χ y J = charVal g (star a • χ) y J * val₂ (ptRos hG oa a) y J (cP D _ χ) g.b := by
  have vv : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) χ y J,
      Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := fun u χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  refine and_congr Iff.rfl ⟨fun h χ y J hJ => ?_, fun h u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · exact (val_corr hJ (h _ (ptRos_isRos hG oa a).1 (ptRos_isRos hG oa a).2 χ) _).symm.trans (vv _ χ y J hJ)
  · exact (vv u χ y J hJ).trans ((congrArg₂ (· * ·) rfl
      (IsRos.unique hG D.P.isAb D.P.isLB ⟨hu, u₀⟩ (ptRos_isRos hG oa a) hJ _ _)).trans (h χ y J hJ).symm)

theorem ptAct_unique (hG : GlobalFnsSt) {oa : D.OAct O} {a : O} {g h h' : GtPtF D F} (e : GtPtAct oa a g h)
    (e' : GtPtAct oa a g h') : h = h' := by
  obtain ⟨b, v⟩ := (ptAct_iff_val hG _ _ _ _).1 e
  obtain ⟨b', v'⟩ := (ptAct_iff_val hG _ _ _ _).1 e'
  exact gt_ext_val (b.trans b'.symm) fun χ y J hJ => (v χ y J hJ).trans (v' χ y J hJ).symm

theorem ptRos_add (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J}
    (hJ : Good D.P.L z J) (x x' w : T ⟶ D.P.A) :
    val₂ (ptRos hG oa a) z J (x * x') w * th D z J x x' (w ≫ oa.onB.act a) =
        th D z J (x ≫ oa.onB.act (star a)) (x' ≫ oa.onB.act (star a)) w *
          (val₂ (ptRos hG oa a) z J x w * val₂ (ptRos hG oa a) z J x' w) ∧
      val₂ (ptRos hG oa a) z J w (x * x') * th D z J w (x ≫ oa.onB.act a) (x' ≫ oa.onB.act a) =
        th D z J (w ≫ oa.onB.act (star a)) x x' *
          (val₂ (ptRos hG oa a) z J w x * val₂ (ptRos hG oa a) z J w x') :=
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  ros_add D.cub hG D.P.isAb _ _ _ (ptRos_isRos hG oa a).1 (ptRos_isRos hG oa a).2 hJ x x' w

theorem exists_ptAct (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) (g : GtPtF D F) : ∃ g', GtPtAct oa a g g' := by
  have := oa.onB.hom (star a)
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ (ptRos hG oa a) (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ (ptRos hG oa a) y J (cP D _ χ) g.b := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
      (LB.pullGen D.P.L _ _ (ptRos hG oa a) (lift (cP D _ χ) g.b).left))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ (ptRos_isRos hG oa a).1 _))
    (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
        (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
      rw [prod_gt, cPoint_act oa]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      have e := (ptRos_add hG oa a hJ 1 1 g.b).1
      rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
      refine (vv 0 y J hJ).trans ?_
      rw [smul_zero, cPoint_zero, mul_eq_left.1 e.symm, _root_.mul_one, charVal_zero g hJ]) (fun χ χ' y J hJ => by
      have e₁ := congrArg Additive.ofMul (ptRos_add hG oa a hJ (cP D _ χ) (cP D _ χ') g.b).1
      have e := charVal_add g hJ (star a • χ) (star a • χ')
      rw [cPoint_act oa, cPoint_act oa] at e
      have e₂ := congrArg Additive.ofMul e
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [smul_add, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at e₁ e₂ ⊢
      linear_combination (norm := abel) e₁ + e₂)
  exact ⟨g', (ptAct_iff_val hG _ _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩⟩

def ptSmul (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) (g : GtPtF D F) : GtPtF D F := (exists_ptAct hG oa a g).choose

variable (hG : GlobalFnsSt) (oa : D.OAct O)

theorem ptAct_ptSmul (a : O) (g : GtPtF D F) : GtPtAct oa a g (ptSmul hG oa a g) := (exists_ptAct hG oa a g).choose_spec

theorem ptAct_iff_eq_ptSmul (a : O) (g g' : GtPtF D F) : GtPtAct oa a g g' ↔ g' = ptSmul hG oa a g :=
  ⟨fun h => ptAct_unique hG h (ptAct_ptSmul hG oa a g), fun h => h ▸ ptAct_ptSmul hG oa a g⟩

theorem ptSmul_b (a : O) (g : GtPtF D F) : (ptSmul hG oa a g).b = g.b ≫ oa.onB.act a := (ptAct_ptSmul hG oa a g).1

theorem ptSmul_val (a : O) (g : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    charVal (ptSmul hG oa a g) χ y J = charVal g (star a • χ) y J * val₂ (ptRos hG oa a) y J (cP D _ χ) g.b :=
  ((ptAct_iff_val hG _ _ _ _).1 (ptAct_ptSmul hG oa a g)).2 χ y J hJ

theorem ptSmul_add (a : O) (g g' : GtPtF D F) : ptSmul hG oa a (g + g') = ptSmul hG oa a g + ptSmul hG oa a g' := by
  have := oa.onB.hom a
  refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩)
  · rw [ptSmul_b, ptSmul_b, ptSmul_b, add_b, MonObj.mul_comp]
  · have e₁ := congrArg Additive.ofMul (ptRos_add hG oa a hJ g.b g'.b (cP D _ χ)).2
    have e := add_val g g' (star a • χ) hJ
    rw [cPoint_act oa] at e
    have e₂ := congrArg Additive.ofMul e
    rw [ptSmul_val hG oa a _ χ hJ, ptSmul_val hG oa a _ χ hJ, ptSmul_val hG oa a _ χ hJ, ptSmul_b, ptSmul_b, add_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂

theorem mul_ptSmul (a a' : O) (g : GtPtF D F) : ptSmul hG oa (a * a') g = ptSmul hG oa a (ptSmul hG oa a' g) := by
  have := oa.onB.hom a'
  have := oa.onB.hom (star a)
  refine gt_ext_val (by rw [ptSmul_b, ptSmul_b, ptSmul_b, oa.onB.map_mul, Category.assoc]) fun χ y J hJ => ?_
  rw [ptSmul_val hG oa _ _ χ hJ, ptSmul_val hG oa _ _ χ hJ, ptSmul_val hG oa _ _ _ hJ,
    IsRos.val_comp hG D.P.isAb D.P.isLB (by rw [star_mul, oa.onB.map_mul]) (oa.onB.map_mul a a')
      (ptRos_isRos hG oa (a * a')) (ptRos_isRos hG oa a) (ptRos_isRos hG oa a') hJ,
    ptSmul_b, cPoint_act oa, star_mul, mul_smul, _root_.mul_assoc]

def ptSmulHom (F : Type) [Field F] [Algebra (FractionRing R) F] (a : O) : GtPtF D F →+ GtPtF D F :=
  AddMonoidHom.mk' (ptSmul hG oa a) (ptSmul_add hG oa a)

theorem iota_act (hB : D.TauBimult) (a : O) (x : D.X) : iota hB F (a • x) = ptSmul hG oa a (iota hB F x) := by
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hbal
  refine gt_ext_val (by rw [ptSmul_b, iota_b, iota_b, cPoint_act oa]) fun χ y J hJ => ?_
  let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
  have e := (val_mul hJ _ _ _).symm.trans
    (val_corr hJ (hbal _ (ptRos_isRos hG oa a).1 (ptRos_isRos hG oa a).2 χ x) κ.left)
  have e' : val (LB.pullGen D.P.L _ _ (ptRos hG oa a) (D.pt2 χ x)) κ.left y J =
      val₂ (ptRos hG oa a) y J (cP D _ χ) (cP D _ x) := by
    rw [val_pull hJ, val₂, ← comp_cP D κ, ← comp_cP D κ x, ← comp_lift]; rfl
  rw [ptSmul_val hG oa _ _ χ hJ, iota_val hB _ _ hJ, iota_val hB _ _ hJ, iota_b, ← e']
  exact ((congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
    (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))).symm

theorem torus_ptSmul {g : GtPtF D F} {t : D.X → F} (h : IsTorusPtF g t) (a : O) :
    IsTorusPtF (ptSmul hG oa a g) fun χ => t (star a • χ) := by
  have := oa.onB.hom a
  obtain ⟨b, v⟩ := (isTorusPtF_iff_val _ _).1 h
  refine (isTorusPtF_iff_val _ _).2 ⟨by rw [ptSmul_b, b, MonObj.one_comp], fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have e := (ptRos_add hG oa a hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  rw [ptSmul_val hG oa a g χ hJ, b, mul_eq_left.1 e.symm, _root_.mul_one]
  exact v _ y J hJ

end Action

section Extension

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']
variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem gtExt_ptSmul {O : Type} [Ring O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O) (a : O)
    (g : GtPtF D F) : gtExt D f hf (ptSmul hG oa a g) = ptSmul hG oa a (gtExt D f hf g) :=
  gt_ext_val (by rw [gtExt_b, ptSmul_b, ptSmul_b, gtExt_b, Category.assoc]) fun χ y J hJ => by
    rw [gtExt_val f hf _ χ hJ, ptSmul_val hG oa _ _ χ hJ, gtExt_val f hf _ _ hJ, gtExt_b, ← comp_cP D (extMap f hf)]
    exact (val_corr hJ ((ptAct_ptSmul hG oa a g).2 _ (ptRos_isRos hG oa a).1 (ptRos_isRos hG oa a).2 χ) _).symm.trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull_pair _ _ hJ _ _)))

theorem gtExt_fixed (σ : F' →+* F') (hσ : σ.comp f = f) (g : GtPtF D F) :
    spMap σ ≫ (gtExt D f hf g).b.left = (gtExt D f hf g).b.left ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ ((gtExt D f hf g).s χ)
      (LB.pullGen D.P.L _ _ ((gtExt D f hf g).s χ) (spMap σ)) := by
  have e : spMap σ ≫ spMap f = spMap f := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]
  obtain ⟨b, v⟩ := (eq_gtExt_iff f hf g _).1 rfl
  refine ⟨by rw [b, ← Category.assoc, e], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine ((val_corr hJ (v χ) _).trans (val_pull hJ _ _ _)).trans (Eq.trans ?_
    ((val_pull hJ _ _ _).trans ((val_corr hJ (v χ) _).trans (val_pull hJ _ _ _))).symm)
  rw [Category.assoc, e]

end Extension

theorem origin_of_generic {S : Scheme.{0}} {V : Type} [CommRing V] [IsDomain V] (B : Over S) (B' : Over (Sp V)) [GrpObj B]
    [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left) (hM : M.IsLB) (hM' : M'.IsLB)
    (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂))
    (q : (𝟙_ (Over (Sp V))).left ⟶ B.left)
    (hq : ∀ I : ULift.{0} (Finset (Fin 2)), ((lift (1 : 𝟙_ (Over (Sp V)) ⟶ B') (1 : 𝟙_ (Over (Sp V)) ⟶ B')).left ≫ β₂) ≫
      (psum B (x2 B) I.down).left = q) (hw : w.IsGen)
    (hgen : ∀ (z : (TK V).left) (J : ((TK V).left ⟶ B.left) → M.ι) (J' : ((TK V).left ⟶ B'.left) → M'.ι), Good M z J →
      Good M' z J' → lamVal w (lift (1 : TK V ⟶ B') (1 : TK V ⟶ B')).left z J J' = 1) :
    ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J →
      Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1 := by
  let O : Over (Sp V) := 𝟙_ (Over (Sp V))
  let e : O.left ⟶ (G2 B').left := (lift (1 : O ⟶ B') 1).left
  let q' : O.left ⟶ B'.left := (1 : O ⟶ B').left
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B' (x2 B') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (NormIso.lift_one_psum B' (T := O) I.down)
  obtain ⟨u, hu⟩ := GlobalTheory.GenOrigin.exists_unit_along M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B' (x2 B') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e q q' hq hq' w hw
  have hval : ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι),
      Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = gm (toUnit T).left z ⊤ u := by
    intro T z J J' hJ hJ'
    have hp : (lift (1 : T ⟶ B') (1 : T ⟶ B')).left = (toUnit T).left ≫ e := by
      show _ = (toUnit T ≫ lift (1 : O ⟶ B') 1).left
      rw [comp_lift, MonObj.comp_one]
    have key : ∀ (p : T.left ⟶ (G2 B').left) (j : (abelian₂ B M).ι) (k : (abelian₂ B' M').ι),
        (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) = j →
        (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B' (x2 B') I.down).left)) = k →
        lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B' M') w p z j k := by
      rintro p _ _ rfl rfl
      rfl
    rw [hp]
    refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
      (funext fun I => ?_)).trans (hu T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
    · rw [← hq I, Category.assoc, Category.assoc]
    · rw [← hq' I, Category.assoc]
  have hK : (toUnit (TK V)).left = jK V := by simpa using Over.w (toUnit (TK V))
  have h1 : (Units.map (jK V).appTop.hom.toMonoidHom u : Γ((TK V).left, ⊤)ˣ) = 1 := unit_ext fun x _ => by
    choose a ha using fun χ : (TK V).left ⟶ B.left => exists_chart hM (χ x)
    choose b hb using fun χ : (TK V).left ⟶ B'.left => exists_chart hM' (χ x)
    have h := (hval (TK V) x a b ha hb).symm.trans (hgen x a b ha hb)
    rw [hK] at h
    rw [map_one]
    exact (gm_pull (𝟙 _) (jK V) x ⊤ trivial u).trans ((congrArg (fun g => gm g x ⊤ u) (Category.id_comp _)).trans h)
  have hu1 : u = 1 := Units.ext (GlobalTheory.GenOrigin.jK_appTop_inj V (by
    have := congrArg Units.val h1
    simpa using this))
  intro T z J J' hJ hJ'
  rw [hval T z J J' hJ hJ', hu1]; exact map_one _

theorem data_c_zero {R : Type} [CommRing R] [IsDomain R] (Q : Data R) : Q.c 0 = 1 :=
  mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))

theorem factor_origin {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D : DegPre R} (hB : D.TauBimult) (F : PFactor Q D) :
    ∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (J' : (T.left ⟶ Q.B.left) → Q.M.L.ι),
      Good D.P.L z J → Good Q.M.L z J' → lamVal F.w (lift (1 : T ⟶ Q.B) (1 : T ⟶ Q.B)).left z J J' = 1 := by
  haveI := F.inc_hom
  haveI := F.o.onB.hom F.f
  refine origin_of_generic D.P.A Q.B D.P.L Q.M.L D.P.isLB Q.M.isLB _ F.w (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left
    (fun I => ?_) F.w_gen fun z J J' hJ hJ' => ?_
  · rw [GlobalTheory.MumRigidZero.lift_comp_left, MonObj.one_comp, MonObj.one_comp]
    exact congrArg (fun z => z.left) (NormIso.lift_one_psum D.P.A (T := 𝟙_ (Over (Sp R))) I.down)
  · have h := F.tau 0 0 z J J' hJ hJ'
    rw [Q.val_tau_zero 0 z J' hJ', map_zero, smul_zero, GlobalTheory.TInj.val_tau_zero_zero D hB z J hJ, data_c_zero,
      MonObj.comp_one, _root_.mul_one] at h
    exact h.symm

theorem seq_pow {U : Type} [CommGroup U] (A L W P c c' c₀ : ℕ → U)
    (hA : ∀ i, A (i + 1) * c' i = A i * A 1) (hL : ∀ i, L (i + 1) * c i = c' i * L i * L 1)
    (hW : ∀ i, W (i + 1) * c i = c₀ i * W i * W 1) (hP : ∀ i, P (i + 1) * c₀ i = P i * P 1) (n : ℕ) :
    A n * L n * (W n * P n)⁻¹ = (A 1 * L 1 * (W 1 * P 1)⁻¹) ^ n := by
  have st : ∀ i, A (i + 1) * L (i + 1) * (W (i + 1) * P (i + 1))⁻¹ =
      A i * L i * (W i * P i)⁻¹ * (A 1 * L 1 * (W 1 * P 1)⁻¹) := fun i => by
    have a₁ := congrArg Additive.ofMul (hA i)
    have a₂ := congrArg Additive.ofMul (hL i)
    have a₃ := congrArg Additive.ofMul (hW i)
    have a₄ := congrArg Additive.ofMul (hP i)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ a₄ ⊢
    linear_combination (norm := abel) a₁ + a₂ - a₃ - a₄
  induction n with
  | zero => rw [pow_zero]; exact mul_eq_right.1 (st 0).symm
  | succ n ih => rw [st, ih, pow_succ]

theorem exists_root {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {R : Type} [CommRing R]
    [IsDomain R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) {n : ℕ}
    (hn : 1 ≤ n) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (hD : DataFrom T iw s ε n Q e) {D : DegPre R} (hB : D.TauBimult)
    (F : PFactor Q D) (a : Q.X) : ∃ d : 𝟙_ (Over (Sp R)) ⟶ Q.B, d ^ n = Q.c a ∧
      ∀ h : GtPtF D (FractionRing R), h.b = (toUnit _ ≫ d) ≫ F.inc → ∀ y z J', Good D.P.L z J' →
        ∃ u, charVal (iota hB (FractionRing R) (F.xi a)) (F.f • F.xi y) z J' =
          u ^ n * charVal (n • h) (F.f • F.xi y) z J' := by
  haveI := F.inc_hom
  haveI := F.o.onB.hom F.f
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, htau⟩ := hD
  have hcomm : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 (Sp R) ≫ spMap iw := by
    rw [Category.assoc, Over.w (T.c₀ (e a))]; simp
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (hpb.1.lift _ _ hcomm) (by simpa using hpb.1.lift_snd _ _ hcomm)
  have hd : d.left ≫ β = spMap iw ≫ (T.c₀ (e a)).left := hpb.1.lift_fst _ _ hcomm
  have key : ∀ k : ℕ, T.c₀ ((k : ℤ) • e a) = T.c₀ (e a) ^ k := fun k => by
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, T.c₀_zero]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, T.c₀_add, ih, pow_succ]
  have hdk : ∀ k : ℕ, (d ^ k).left ≫ β = spMap iw ≫ (T.c₀ ((k : ℤ) • e a)).left := fun k => by
    rw [key]; exact GlobalTheory.FrameMove.pow_comm hpb hd k
  have hdn : d ^ n = Q.c a :=
    Over.OverMorphism.ext (hpb.1.hom_ext ((hdk n).trans (hc a).symm) ((Over.w _).trans (Over.w _).symm))
  refine ⟨d, hdn, fun h hb y z J' hJ' => ?_⟩
  have hw0 : ∀ (T' : Over (Sp R)) z J J', Good T.M.L z J → Good Q.M.L z J' →
      lamVal w (lift (1 : T' ⟶ Q.B) (1 : T' ⟶ Q.B)).left z J J' = 1 := by
    refine GlobalTheory.GenOrigin.lamVal_origin_of_generic T.B Q.B T.M.L Q.M.L T.M.isLB Q.M.isLB _ β β₂ w hpb hsq hw
      fun z J J' hJ hJ' => ?_
    obtain ⟨k, hk, hv⟩ := htau 0 0
    have h := hv z J J' hJ hJ'
    have k1 : k = 1 := by
      ext
      rw [hk]
      simp
    have e0 : ((n : ℤ) • e 0) = 0 := by rw [map_zero, smul_zero]
    rw [k1, Q.val_tau_zero 0 z J' hJ', e0, GlobalTheory.TInj.val_τ₀_zero_at T _ z J hJ, data_c_zero, MonObj.comp_one] at h
    have u1 : unitOn (1 : (FractionRing R)ˣ) = 1 := map_one _
    simp only [u1, map_one, _root_.one_mul, _root_.mul_one] at h
    exact h.symm
  let Z : Over (Sp R) := TF (R := R) (FractionRing R)
  let Z₀ : Over (Sp W) := Over.mk (Z.hom ≫ spMap iw)
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt Q.M.isLB z
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt T.M.isLB z
  let x : Z ⟶ Q.B := toUnit Z ≫ d
  let v : Z ⟶ Q.B := toUnit Z ≫ Q.c y
  let χ := F.f • F.xi y
  have hχ : cP D Z χ = v ≫ F.inc ≫ F.o.onB.act F.f := by
    rw [cPoint_act F.o, cP, F.c_xi]; simp only [v, Category.assoc]
  have up : ∀ (p : 𝟙_ (Over (Sp R)) ⟶ Q.B) (p₀ : 𝟙_ (Over (Sp W)) ⟶ T.B), p.left ≫ β = spMap iw ≫ p₀.left →
      (toUnit Z₀ ≫ p₀).left = (toUnit Z ≫ p).left ≫ β := fun p p₀ hp => by
    show (Z.hom ≫ spMap iw) ≫ p₀.left = (Z.hom ≫ p.left) ≫ β
    rw [Category.assoc, Category.assoc, hp]
  have S := seq_pow (U := (Z.left.presheaf.stalk z)ˣ) (fun i => charVal (i • h) χ z J')
    (fun i => lamVal F.w (lift (x ^ i) v).left z J' J) (fun i => lamVal w (lift (x ^ i) v).left z J₀ J)
    (fun i => val (T.τ₀ ((i : ℤ) • e a) ((n : ℤ) • e y)) (toUnit Z₀).left z J₀)
    (fun i => cubV Q.cub z J (x ^ i) x v) (fun i => cubV D.cub z J' (h.b ^ i) h.b (cP D Z χ))
    (fun i => cubV T.cub (T := Z₀) z J₀ (toUnit Z₀ ≫ T.c₀ ((i : ℤ) • e a)) (toUnit Z₀ ≫ T.c₀ (e a))
      (toUnit Z₀ ≫ T.c₀ ((n : ℤ) • e y)))
    (fun i => by
      have C : IsCub (th D (T := Z) z J') := isCub_cubV D.cub hJ'
      have t := add_val (i • h) h χ hJ'
      rw [nsmul_b, C.s01, C.s12, ← succ_nsmul] at t
      simp only [one_nsmul]
      exact t)
    (fun i => by
      have t := GlobalTheory.MumfordE8Bimultiplicative.lamVal_law₁ Q.B D.P.A Q.M _ Q.cub D.cub Q.isAb F.inc (F.inc ≫ F.o.onB.act F.f) F.w F.w_gen
        (factor_origin hB F) Z (x ^ i) x v z J' J hJ' hJ
      rw [← pow_succ, ← hχ, MonObj.pow_comp, ← show h.b = x ≫ F.inc from hb] at t
      simp only [pow_one]
      exact t)
    (fun i => by
      have t := (GlobalTheory.LamRigid.lam_iso_laws _ _ T.B Q.B T.M Q.M T.cub Q.cub (spMap iw) β β₂ w hpb Q.isAb hsq hw hw0 Z
        (x ^ i) x v z J₀ J hJ₀ hJ).2 (toUnit Z₀ ≫ T.c₀ ((i : ℤ) • e a)) (toUnit Z₀ ≫ T.c₀ (e a))
        (toUnit Z₀ ≫ T.c₀ ((n : ℤ) • e y)) (by rw [up _ _ (hdk i), MonObj.comp_pow]) (up _ _ hd) (up _ _ (hc y))
      rw [← pow_succ] at t
      simp only [pow_one]
      exact t)
    (fun i => by
      have t := GlobalTheory.TChart.PeriodAdd.val_τ₀_add T Z₀ (z := z) (J := J₀) hJ₀ ((i : ℤ) • e a) (e a) ((n : ℤ) • e y)
      have g : ∀ p p' : Fin T.r → ℤ, p = p' → val (T.τ₀ p ((n : ℤ) • e y)) (toUnit Z₀).left z J₀ =
          val (T.τ₀ p' ((n : ℤ) • e y)) (toUnit Z₀).left z J₀ := by rintro _ _ rfl; rfl
      rw [g ((i : ℤ) • e a + e a) (((i + 1 : ℕ) : ℤ) • e a) (by rw [Nat.cast_succ, add_smul, one_smul]),
        g (e a) (((1 : ℕ) : ℤ) • e a) (by rw [Nat.cast_one, one_smul])] at t
      exact t) n
  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp only [jFK, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  let ρ : Z ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  have hl : (lift (x ^ n) v).left = (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c y)).left := by
    have : lift (x ^ n) v = ρ ≫ lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c y) := by
      rw [comp_lift, ← Category.assoc, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit Z), ← hdn, MonObj.comp_pow]
    rw [this, Over.comp_left, show ρ.left = 𝟙 _ from hj]
    exact Category.id_comp _
  have hr : (toUnit Z₀).left = (TK R).hom ≫ spMap iw := by
    show (jFK (R := R) (FractionRing R) ≫ jK R) ≫ spMap iw = jK R ≫ spMap iw
    rw [hj]; exact congrArg (· ≫ spMap iw) (Category.id_comp _)
  have ht : charVal (iota hB (FractionRing R) (F.xi a)) χ z J' = val (D.tau (F.xi a) χ) (𝟙 _) z J' := by
    rw [iota_val hB _ _ hJ', tauVal, hj]
    exact congrArg (fun r => val (D.tau (F.xi a) χ) r z J') (Category.id_comp _)
  obtain ⟨k, hk, hv⟩ := htau a y
  have hk' : (k : FractionRing R) = (∏ i, algebraMap R (FractionRing R) (s i) ^ (ε i (e a) (e y))) ^ n := by
    rw [hk, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]
  have h0 : (∏ i, algebraMap R (FractionRing R) (s i) ^ (ε i (e a) (e y))) ≠ 0 := fun h0 =>
    k.ne_zero (by rw [hk', h0, zero_pow (by omega)])
  obtain rfl : k = Units.mk0 _ h0 ^ n := Units.ext (by rw [hk', Units.val_pow_eq_pow_val, Units.val_mk0])
  have t₁ := hv z J₀ J hJ₀ hJ
  have t₂ := F.tau a y z J' J hJ' hJ
  have t₃ : gm (𝟙 (TK R).left) z ⊤ (unitOn (Units.mk0 _ h0 ^ n)) = stalkUnits (F := FractionRing R) z (Units.mk0 _ h0) ^ n :=
    (gm_unitOn (F := FractionRing R) z _).trans (map_pow _ _ _)
  have alg : ∀ {U : Type} [CommGroup U] {q k A L W P E t : U}, q = k ^ n * (W * P) → q = L * t →
      A * L * (W * P)⁻¹ = E ^ n → t = (k * E⁻¹) ^ n * A := by
    intro U _ q k A L W P E t h₁ h₂ h₃
    rw [mul_pow, inv_pow, ← h₃]
    have a₁ := congrArg Additive.ofMul (h₂.symm.trans h₁)
    apply Additive.ofMul.injective
    generalize k ^ n = m at a₁ ⊢
    simp only [ofMul_mul, ofMul_inv] at a₁ ⊢
    linear_combination (norm := abel) a₁
  beta_reduce at S
  rw [hl, hr] at S
  rw [t₃] at t₁
  exact ⟨_, ht.trans (alg (U := (Z.left.presheaf.stalk z)ˣ) t₁ t₂ S)⟩

theorem exists_hom_root {X U : Type} [AddCommGroup X] [Module.Free ℤ X] [CommGroup U] (n : ℕ) (t : Multiplicative X →* U)
    (h : ∀ x, ∃ u, t x = u ^ n) : ∃ r : Multiplicative X →* U, r ^ n = t := by
  let b := Module.Free.chooseBasis ℤ X
  choose u hu using h
  let l : X →ₗ[ℤ] Additive U := b.constr ℤ fun i => Additive.ofMul (u (Multiplicative.ofAdd (b i)))
  have : n • l = t.toAdditiveRight.toIntLinearMap := b.ext fun i => by
    rw [LinearMap.smul_apply, b.constr_basis, ← ofMul_pow, ← hu]; rfl
  exact ⟨l.toAddMonoidHom.toMultiplicativeLeft, MonoidHom.ext fun x =>
    congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)⟩

theorem exists_rational {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {R : Type} [CommRing R]
    [IsDomain R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) {n : ℕ}
    (hn : 1 ≤ n) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (hD : DataFrom T iw s ε n Q e) {D : DegPre R} (hB : D.TauBimult)
    (F : PFactor Q D) (a : Q.X) : ∃ h : GtPtF D (FractionRing R), n • h = iota hB _ (F.xi a) ∧
      ptSmul GlobalTheory.globalFns_holds F.o F.e h = h := by
  haveI := F.inc_hom
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨d, hdn, hd⟩ := exists_root T iw s ε hn Q e hD hB F a
  let E := ptSmulHom hG F.o (FractionRing R) F.e
  have EE : ∀ g, E (E g) = E g := fun g => (mul_ptSmul hG F.o F.e F.e g).symm.trans (by rw [F.idem]; rfl)
  have Ei : E (iota hB _ (F.xi a)) = iota hB _ (F.xi a) :=
    (iota_act hG F.o hB F.e (F.xi a)).symm.trans (by rw [← F.xi_xp, F.xp_xi])
  obtain ⟨h₁, hb₁⟩ := exists_lift (D := D) (F := FractionRing R) ((toUnit _ ≫ d) ≫ F.inc)
  have hb : (E h₁).b = (toUnit _ ≫ d) ≫ F.inc := by
    refine (ptSmul_b hG F.o F.e h₁).trans ?_
    rw [hb₁, ← F.pr_inc, Category.assoc, ← Category.assoc F.inc, F.inc_pr, Category.id_comp]
  let g := iota hB (FractionRing R) (F.xi a) - n • E h₁
  have Eg : E g = g := by rw [map_sub, map_nsmul, EE, Ei]
  have gb : g.b = 1 := by
    rw [show g = iota hB (FractionRing R) (F.xi a) + -(n • E h₁) from sub_eq_add_neg _ _, add_b, neg_b, nsmul_b, hb, iota_b,
      ← MonObj.pow_comp, ← MonObj.comp_pow, hdn, cP, F.c_xi, Category.assoc, mul_inv_cancel]
  obtain ⟨t, ht⟩ := exists_isTorusPtF_of_b gb
  have ht' := torus_ptSmul hG F.o ht F.e
  rw [show ptSmul hG F.o F.e g = g from Eg] at ht'
  have te : ∀ χ, t (Multiplicative.ofAdd χ) = t (Multiplicative.ofAdd (star F.e • χ)) := fun χ =>
    Units.ext (congrFun (ht.fun_unique ht') χ)
  obtain ⟨r, rfl⟩ := exists_hom_root n t fun χ => by
    obtain ⟨y, hy⟩ := F.onto χ.toAdd
    obtain ⟨z, J, hJ⟩ := exists_good_chart D (FractionRing R)
    have C : IsCub (th D (T := TF (R := R) (FractionRing R)) z J) := isCub_cubV D.cub hJ
    obtain ⟨u, hu⟩ := hd (E h₁) hb y z J hJ
    have k := add_val g (n • E h₁) (F.f • F.xi y) hJ
    rw [gb, C.face₂, _root_.mul_one, show g + n • E h₁ = iota hB (FractionRing R) (F.xi a) from sub_add_cancel _ _, hu] at k
    have k' := torusPt_val t (F.f • F.xi y) hJ
    rw [← (isTorusPtF_iff_eq g t).1 ht, ← mul_right_cancel k] at k'
    refine ⟨(stalkUnits (F := FractionRing R) z).symm u, ?_⟩
    rw [← map_pow, k', MulEquiv.symm_apply_apply, te (F.f • F.xi y), ← hy, ← te]
    rfl
  refine ⟨E (E h₁ + torusPt D (FractionRing R) (Additive.ofMul r)), ?_, EE _⟩
  rw [← map_nsmul, nsmul_add, ← map_nsmul (torusPt D (FractionRing R)), ← ofMul_pow, ← (isTorusPtF_iff_eq g _).1 ht, add_sub_cancel, Ei]

theorem exists_fixed_root : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)), ∀ a : Q.X, ∃ h : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), (spMap σ.toAlgHom.toRingHom ≫ h.b.left = h.b.left ∧ ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (h.s χ) (LB.pullGen D'.toPre.P.L _ _ (h.s χ) (spMap σ.toAlgHom.toRingHom))) ∧ (∃ z : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtF.IsNsmul n h z ∧ GtPtF.IsIota (F.xi a) z) ∧ GtPtAct F.o F.e h h := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ _ _ Q e hD _ D' F σ a
  obtain ⟨h, hn', he⟩ := exists_rational T iw s ε hn Q e hD D'.tau_bimult F a
  have hf : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
      (algebraMap (FractionRing R) (FractionRing R)) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) :=
    RingHom.ext fun _ => rfl
  refine ⟨gtExt D'.toPre _ hf h, gtExt_fixed _ hf _ (RingHom.ext fun x => σ.commutes x) h,
    ⟨iota D'.tau_bimult _ (F.xi a), (isNsmul_iff_eq _ _ _).2 ?_, isIota_iota _ _⟩,
    (ptAct_iff_eq_ptSmul GlobalTheory.globalFns_holds F.o F.e _ _).2 ?_⟩
  · rw [← map_nsmul, hn', gtExt_iota]
  · rw [← gtExt_ptSmul, he]

end GlobalTheory.Mum.EDiv
