import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

structure Ray (oa : D.OAct O) : Type 1 where

  H : Over (Sp R)
  [grp : GrpObj H]
  [comm : IsCommMonObj H]

  Φ : ∀ T, (T ⟶ H) ≃ GtPt D T
  isGt : (splitExt D).IsGt H
  rep : Represents Φ

  ρ : RingAct H O
  smul : ∀ (a : O) T (x : T ⟶ H), FormalPoint.IsSmulPt oa a (Φ T x) (Φ T (x ≫ ρ.act a))

attribute [instance] Ray.grp Ray.comm

instance (oa : D.OAct O) : Nonempty (Ray oa) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (splitExt D)
  obtain ⟨Φ, hΦ⟩ := exists_points hL hH
  obtain ⟨ρ, hρ⟩ := exists_ringAct hL oa (Φ := Φ) hΦ
  exact ⟨{ H := H, Φ := Φ, isGt := hH, rep := hΦ, ρ := ρ, smul := hρ }⟩

def Chr (D : DegPre R) : Type := D.X

instance : AddCommGroup (Chr D) := inferInstanceAs (AddCommGroup D.X)

instance : Module O (Chr D) := Module.compHom D.X (starRingEnd O)

variable (D O) in

def torAct : OAct O (splitTorus (Sp R) (Chr D)) := Diag.diagAct (Sp R) O (Chr D)

theorem exists_torPt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) (Chr D)) : ∃ g : GtPt D T, g.b = 1 ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      (val (g.s χ) r y J).val = gs r y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  let u : Multiplicative D.X →* Γ(T.left, ⊤) :=
    { toFun := fun χ => (coord x).hom (AddMonoidAlgebra.single χ.toAdd 1)
      map_one' := Diag.coord_single_zero x
      map_mul' := fun a b => Diag.coord_single_add x _ _ }
  let v : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) := fun χ =>
    ⟨fun _ => res le_top (u.toHomUnits (Multiplicative.ofAdd χ))⟩
  have hv : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (v χ) r y J = gm r y ⊤ (u.toHomUnits (Multiplicative.ofAdd χ)) := fun χ Z r y J hJ =>
    gm_res r y _ (hJ.mem PEmpty.elim r) _
  obtain ⟨g, hb, hg⟩ := exists_pt (1 : T ⟶ D.P.A) v (fun χ i j => by
      obtain rfl : i = j := funext fun k => k.elim
      have e : (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
        dsimp only [LB.LinComb]
        erw [Fintype.prod_empty]
        rfl
      rw [e, _root_.one_mul])
    (fun χ U _ h => by
      rw [prod_pt, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel])
    (fun y J hJ => by rw [hv _ _ _ _ _ hJ, ofAdd_zero, map_one, map_one])
    (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, _root_.mul_one, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, ofAdd_add, map_mul, map_mul])
  exact ⟨g, hb, fun χ Z r y J hJ => by
    rw [hg _ _ _ _ _ hJ, hv _ _ _ _ _ hJ]; exact (gs_unit r y ⊤ trivial _).symm⟩

namespace Ray

variable {oa : D.OAct O} (Y : Ray oa)

def act : OAct O Y.H := ofRingAct Y.ρ

variable (oa) in

def actB : OAct O D.P.A := ofRingAct oa.onB.toRingAct

def q : Y.H ⟶ D.P.A := (Y.Φ Y.H (𝟙 _)).b

theorem Φ_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

theorem q_linear : IsLinearHom Y.act (actB oa) Y.q :=
  ⟨isMonHom_of_mul _ fun T x x' => by
      rw [← Φ_b, ← Φ_b, ← Φ_b]; exact ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x x')).1,
    fun a => by
      have h := (Y.smul a _ (𝟙 _)).1
      rw [Φ_b, Category.id_comp] at h
      exact h⟩

def i : splitTorus (Sp R) (Chr D) ⟶ Y.H := (Y.Φ _).symm (exists_torPt (𝟙 _)).choose

theorem Φ_i {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) (Chr D)) : (Y.Φ T (x ≫ Y.i)).b = 1 ∧
    ∀ (χ : D.X) y J, Good D.P.L y J →
      (cv (Y.Φ T (x ≫ Y.i)) χ y J).val = gs (𝟙 _) y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  obtain ⟨h₁, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T _ x Y.i)
  obtain ⟨e₁, e₂⟩ := (exists_torPt (D := D) (𝟙 _)).choose_spec
  have e : Y.Φ _ Y.i = (exists_torPt (D := D) (𝟙 _)).choose := Equiv.apply_symm_apply _ _
  rw [e] at h₁ h₂
  refine ⟨by rw [h₁, e₁, MonObj.comp_one], fun χ y J hJ => ?_⟩
  rw [h₂ χ y J hJ, e₂ χ _ _ y J hJ]
  conv_rhs => rw [← Category.comp_id x, coord_comp]
  exact (gs_eq x.left y ⊤ trivial _).trans (gs_eq (𝟙 _) y ⊤ trivial _).symm

theorem i_q : Y.i ≫ Y.q = 1 := by
  have h := (Y.Φ_i (𝟙 _)).1
  rwa [Φ_b, Category.id_comp] at h

theorem i_linear : IsLinearHom (torAct D O) Y.act Y.i := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  refine ⟨isMonHom_of_mul _ fun T x x' => (Y.Φ T).injective ?_, fun a => (Y.Φ _).injective ?_⟩
  · refine isAdd_unique ((TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => Units.ext ?_⟩) (Y.rep.2 T _ _)
    · rw [(Y.Φ_i _).1, (Y.Φ_i _).1, (Y.Φ_i _).1, _root_.mul_one]
    · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [(Y.Φ_i x').1, C.face₃, _root_.mul_one, Units.val_mul, (Y.Φ_i _).2 χ y J hJ, (Y.Φ_i _).2 χ y J hJ,
        (Y.Φ_i _).2 χ y J hJ]
      exact (congrArg (gs _ y ⊤) (Diag.coord_mul x x' χ)).trans (gs_mul (𝟙 _) y ⊤ trivial _ _)
  · obtain ⟨h₁, h₂⟩ := (isSmulPt_iff hL oa a _ _).1 (Y.smul a _ (𝟙 _ ≫ Y.i))
    have := oa.onB.hom a
    have := oa.onB.hom (star a)
    rw [Category.id_comp] at h₁ h₂
    have k := Y.Φ_i (𝟙 _)
    rw [Category.id_comp] at k
    refine pt_ext ?_ fun χ y J hJ => Units.ext ?_
    · exact (Y.Φ_i _).1.trans (h₁.trans (by rw [k.1, MonObj.one_comp])).symm
    · have C : IsCub (th D (T := splitTorus (Sp R) (Chr D)) y J) := isCub_cubV D.cub hJ
      have e := (rosGen_add hL oa a hJ 1 1 (cP D _ χ)).2
      rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
      refine ((Y.Φ_i _).2 χ y J hJ).trans (Eq.trans ?_ (congrArg Units.val (h₂ χ y J hJ)).symm)
      rw [k.1, mul_eq_left.1 e.symm, _root_.mul_one, k.2 _ y J hJ]
      refine congrArg (gs _ y ⊤) ?_
      have := Diag.coord_comp_diagMap_single (𝟙 (splitTorus (Sp R) (Chr D)))
        (DistribSMul.toAddMonoidHom (Chr D) a) χ
      rw [Category.id_comp] at this
      exact this

theorem isKernel : IsPullback Y.i (toUnit _) Y.q η[D.P.A] := by
  have ex : ∀ {T : Over (Sp R)} y, ∃ J, Good D.P.L (Z := T.left) y J := fun y => by
    choose I hI using fun χ => exists_chart D.P.isLB ((χ : _ ⟶ D.P.A.left) y)
    exact ⟨I, hI⟩
  refine Diag.isPullback_toUnit_of_lift _ Y.i_q (fun {T} a b h => Diag.hom_ext fun χ => fn_ext fun y _ => ?_)
    fun {T} x hx => ?_
  · obtain ⟨J, hJ⟩ := ex y
    exact ((Y.Φ_i a).2 χ y J hJ).symm.trans (h ▸ (Y.Φ_i b).2 χ y J hJ)
  · have hb : (Y.Φ T x).b = 1 := (Y.Φ_b x).trans hx
    have hF : ∀ χ, FormEq (DegPre.gtφT D T (Y.Φ T x).b χ) DegPre.gtε (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun χ U _ h => by
        rw [prod_pt, hb, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
    choose s _ vs using fun χ => exists_gen D.P.isLB (hF χ) _ ((Y.Φ T x).isGen χ)
    have le : (⊤ : T.left.Opens) ≤ LB.wchart D.P.L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun _ _ => Set.mem_iInter.2 fun k => k.elim
    let u : D.X → Γ(T.left, ⊤)ˣ := fun χ => res le ((s χ).s PEmpty.elim)
    have hu : ∀ χ y J, Good D.P.L y J → gs (𝟙 _) y ⊤ (u χ).val = (cv (Y.Φ T x) χ y J).val := fun χ y J hJ =>
      (gs_unit _ y ⊤ trivial _).trans (congrArg Units.val ((gm_res _ y le trivial _).trans
        ((val_of (s χ) _ y J PEmpty.elim fun k => k.elim).symm.trans (vs χ _ _ y J hJ))))
    let g : Multiplicative (Chr D) →* Γ(T.left, ⊤) :=
      { toFun := fun χ => (u χ.toAdd).val
        map_one' := fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          refine (hu 0 y J hJ).trans ?_
          rw [cv_zero _ hJ, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
        map_mul' := fun a b => fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
          have e := cv_add (Y.Φ T x) hJ a.toAdd b.toAdd
          rw [hb, C.face₃, _root_.mul_one] at e
          refine (hu _ y J hJ).trans (Eq.trans ?_ (gs_mul _ y ⊤ trivial _ _).symm)
          exact (congrArg Units.val e).trans (congrArg₂ (· * ·) (hu _ y J hJ) (hu _ y J hJ)).symm }
    refine ⟨Diag.ofChar T g, (Y.Φ T).injective (pt_ext ((Y.Φ_i _).1.trans hb.symm) fun χ y J hJ => Units.ext ?_)⟩
    exact ((Y.Φ_i _).2 χ y J hJ).trans ((congrArg (gs _ y ⊤) (Diag.coord_ofChar T g χ)).trans (hu χ y J hJ))

end Ray

end Ray

section Eig

variable {R S O : Type} [CommRing R] [CommRing S] [CommRing O] (f : R →+* S)
  {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

abbrev LieAt (a : OAct O G) : Type := Lie (a.pullback (spMap f))

abbrev LieEig (a : OAct O G) (σ : O →+* S) : Type := Lie.eig (a.pullback (spMap f)) σ

theorem isLinearHom_pull {a : OAct O G} {a' : OAct O G'} {φ : G ⟶ G'} (h : IsLinearHom a a' φ) :
    IsLinearHom (a.pullback (spMap f)) (a'.pullback (spMap f)) ((Over.pullback (spMap f)).map φ) :=
  haveI := h.isMonHom
  ⟨inferInstance, fun x => ((Over.pullback (spMap f)).map_comp _ _).symm.trans
    ((congrArg _ (h.comm x)).trans ((Over.pullback (spMap f)).map_comp _ _))⟩

def lieMap {a : OAct O G} {a' : OAct O G'} {φ : G ⟶ G'} (h : IsLinearHom a a' φ) : LieAt f a →ₗ[S] LieAt f a' :=
  haveI := h.isMonHom
  Lie.map _ _ ((Over.pullback (spMap f)).map φ)

theorem hom_lieMap {a : OAct O G} {a' : OAct O G'} {φ : G ⟶ G'} (h : IsLinearHom a a' φ) (v : LieAt f a) :
    (lieMap f h v).hom = v.hom ≫ (Over.pullback (spMap f)).map φ := rfl

theorem lieMap_act {a : OAct O G} {a' : OAct O G'} {φ : G ⟶ G'} (h : IsLinearHom a a' φ) (x : O) (v : LieAt f a) :
    lieMap f h (x • v) = x • lieMap f h v :=
  haveI := h.isMonHom
  Lie.map_act_smul (isLinearHom_pull f h) x v

def eigMap {a : OAct O G} {a' : OAct O G'} {φ : G ⟶ G'} (h : IsLinearHom a a' φ) (σ : O →+* S) :
    LieEig f a σ →ₗ[S] LieEig f a' σ :=
  (lieMap f h).restrict fun v hv x => by rw [← lieMap_act, hv x, map_smul]

theorem coe_eigMap {a : OAct O G} {a' : OAct O G'} {φ : G ⟶ G'} (h : IsLinearHom a a' φ) (σ : O →+* S)
    (v : LieEig f a σ) : (eigMap f h σ v).1 = lieMap f h v.1 := rfl

def tanPt {a : OAct O G} (v : LieAt f a) : Over.mk ((epsR S).hom ≫ spMap f) ⟶ G :=
  HTLat.pushEquiv (isGrpPullback_pullback G (spMap f)) _ v.hom

end Eig

end GlobalTheory.RayEv
