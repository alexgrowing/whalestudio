import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusModel GlobalTheory.AdicColimit GlobalTheory.EigenSplit GlobalTheory.HTLat Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def raynaud : Over (Sp R) := (exists_comparison U).choose

instance raynaudGrp : GrpObj (raynaud U) := (exists_comparison U).choose_spec.choose

instance raynaudComm : IsCommMonObj (raynaud U) := (exists_comparison U).choose_spec.choose_spec.choose

def raynaudPts : ∀ T, (T ⟶ raynaud U) ≃ GtPt D.toPre T := (exists_comparison U).choose_spec.choose_spec.choose_spec.choose

def raynaudCmp : ∀ T, IsAdicColimit I T → ((T ⟶ raynaud U) ≃* (T ⟶ G)) :=
  (exists_comparison U).choose_spec.choose_spec.choose_spec.choose_spec.choose

theorem raynaud_spec : (splitExt D.toPre).IsGt (raynaud U) ∧ Represents (raynaudPts U) ∧
    (∀ T hT w x, raynaudCmp U T hT w = x ↔ FormalPoint.IsPointOf U (raynaudPts U T w) x) ∧
    ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ raynaud U), raynaudCmp U T' hT' (k ≫ x) = k ≫ raynaudCmp U T hT x :=
  (exists_comparison U).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

variable {Λ : Type} [CommRing Λ] [StarRing Λ] [Module Λ D.toPre.X] (ιD : D.toPre.OAct Λ)

def raynaudAct : RingAct (raynaud U) Λ :=
  (exists_ringAct GlobalTheory.allSixLaws.1.globalFns ιD (Φ := raynaudPts U) (raynaud_spec U).2.1).choose

theorem raynaudAct_spec (a : Λ) (T : Over (Sp R)) (x : T ⟶ raynaud U) :
    FormalPoint.IsSmulPt ιD a (raynaudPts U T x) (raynaudPts U T (x ≫ (raynaudAct U ιD).act a)) :=
  (exists_ringAct GlobalTheory.allSixLaws.1.globalFns ιD (Φ := raynaudPts U) (raynaud_spec U).2.1).choose_spec a T x

theorem raynaudCmp_act {ιA : A.OAct Λ} {ιG : RingAct G Λ} (hO : U.OLinear Λ ιD ιA ιG) (T : Over (Sp R))
    (hT : IsAdicColimit I T) (x : T ⟶ raynaud U) (a : Λ) :
    raynaudCmp U T hT (x ≫ (raynaudAct U ιD).act a) = raynaudCmp U T hT x ≫ ιG.act a :=
  ((raynaud_spec U).2.2.1 _ hT _ _).2 ((((raynaud_spec U).2.2.1 _ hT x _).1 rfl).smul GlobalTheory.allSixLaws.1.globalFns hO a
    (raynaudAct_spec U ιD a _ _))

end Raynaud

namespace Point

open OmegaRank

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem existsUnique_corr_dual : (∀ y : specO O (DualNumber O) ⟶ P.G, ∃! x, Corr P x y) ∧
    ∀ x : specO O (DualNumber O) ⟶ P.Gt, ∃! y, Corr P x y := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have hc := isAdicComplete_dualNumber (O := O) p
  exact ⟨existsUnique_left (P := P) hp hc, existsUnique_right (P := P) hp hc⟩

theorem exists_lieCmp : ∃ e : LieG P.Gt ≃ LieG P.G, ∀ x, Corr P x.1 (e x).1 := by
  haveI := P.isLocalRing
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  obtain ⟨hl, hr⟩ := P.existsUnique_corr_dual
  let f : LieG P.G → LieG P.Gt := fun y => ⟨(hl y.1).choose,
    (existsUnique_left (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hl y.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [y.2] at h
        exact h) Corr.one⟩
  let g : LieG P.Gt → LieG P.G := fun x => ⟨(hr x.1).choose,
    (existsUnique_right (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hr x.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [x.2] at h
        exact h) Corr.one⟩
  have hf : ∀ y, Corr P (f y).1 y.1 := fun y => (hl y.1).choose_spec.1
  have hg : ∀ x, Corr P x.1 (g x).1 := fun x => (hr x.1).choose_spec.1
  exact ⟨⟨g, f, fun x => Subtype.ext ((hl _).unique (hf _) (hg x)),
    fun y => Subtype.ext ((hr _).unique (hg _) (hf y))⟩, hg⟩

def lieCmp : LieG P.Gt ≃ LieG P.G := P.exists_lieCmp.choose

theorem eq_lieCmp_iff (x : LieG P.Gt) (y : specO O (DualNumber O) ⟶ P.G) : y = (P.lieCmp x).1 ↔ Corr P x.1 y :=
  ⟨fun h => h ▸ P.exists_lieCmp.choose_spec x,
    fun h => (P.existsUnique_corr_dual.2 x.1).unique h (P.exists_lieCmp.choose_spec x)⟩

theorem corr_lieCmp (x : LieG P.Gt) : Corr P x.1 (P.lieCmp x).1 := (P.eq_lieCmp_iff x _).1 rfl

theorem lieCmp_add (x y : LieG P.Gt) : P.lieCmp (lieAdd x y) = lieAdd (P.lieCmp x) (P.lieCmp y) :=
  Subtype.ext ((P.eq_lieCmp_iff (lieAdd x y) ((P.lieCmp x).1 * (P.lieCmp y).1)).2
    ((P.corr_lieCmp x).mul (P.corr_lieCmp y))).symm

theorem lieCmp_scale (c : O) (x : LieG P.Gt) :
    P.lieCmp (AvDefs.lieScale P.Gt c x) = AvDefs.lieScale P.G c (P.lieCmp x) :=
  Subtype.ext ((P.eq_lieCmp_iff (AvDefs.lieScale P.Gt c x) (ptMap (dualScale c) ≫ (P.lieCmp x).1)).2
    ((P.corr_lieCmp x).comp (dualScale c))).symm

def omegaCmp : omega P.G ≃ₗ[O] omega P.Gt where
  toFun f := ⟨f.1 ∘ P.lieCmp,
    fun x y _ => (congrArg f.1 (P.lieCmp_add x y)).trans (omega_lieAdd f _ _),
    fun c x _ => (congrArg f.1 (P.lieCmp_scale c x)).trans (omega_lieScale f _ _)⟩
  invFun f := ⟨f.1 ∘ P.lieCmp.symm,
    fun x y _ => (congrArg f.1 (P.lieCmp.symm_apply_eq.2 (by
      rw [lieCmp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; rfl))).trans (omega_lieAdd f _ _),
    fun c x _ => (congrArg f.1 (P.lieCmp.symm_apply_eq.2 (by
      rw [lieCmp_scale, Equiv.apply_symm_apply]; rfl))).trans (omega_lieScale f _ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (funext fun x => congrArg f.1 (P.lieCmp.apply_symm_apply x))
  right_inv f := Subtype.ext (funext fun x => congrArg f.1 (P.lieCmp.symm_apply_apply x))

theorem omegaCmp_apply (f : omega P.G) (x : LieG P.Gt) : (P.omegaCmp f).1 x = f.1 (P.lieCmp x) := rfl

end Point

end GlobalTheory.HTLat

namespace GlobalTheory.LocM

section Field

variable {p : ℕ} (C : SCF p)

abbrev fldVal : Valuation ↥C.S ℝ≥0 := NormedField.valuation (K := ↥C.S)

theorem integers_intO : (fldVal C).Integers ↥(intO ↥C.S) where
  hom_inj := Subtype.val_injective
  map_le_one x := by
    rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
    exact x.2
  exists_of_le_one r hr := ⟨⟨r, by
    rw [NormedField.valuation_apply, ← NNReal.coe_le_coe] at hr
    exact hr⟩, rfl⟩

variable [Fact p.Prime]

theorem norm_p_lt_one : ‖algebraMap ↥(intO ↥C.S) ↥C.S (p : ↥(intO ↥C.S))‖ < 1 := by
  rw [map_natCast, C.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

instance factNotIsUnitIntO : Fact ¬IsUnit (p : ↥(intO ↥C.S)) :=
  ⟨fun h => (norm_p_lt_one C).ne ((NormIntegers.isUnit_iff_norm_eq_one (integers_intO C)).1 h)⟩

instance isAdicCompleteIntO : IsAdicComplete (Ideal.span {(p : ↥(intO ↥C.S))}) ↥(intO ↥C.S) :=
  NormIntegers.isAdicComplete_span_singleton (integers_intO C) (norm_p_lt_one C)

def padicEmb : ℚ_[p] →+* ↥C.S := (exists_padic_isometry p C.norm_p).choose

theorem norm_padicEmb (x : ℚ_[p]) : ‖padicEmb C x‖ = ‖x‖ := (exists_padic_isometry p C.norm_p).choose_spec x

instance padicIntAlgebra : Algebra ℤ_[p] ↥C.S := ((padicEmb C).comp PadicInt.Coe.ringHom).toAlgebra

instance padicIntAlgebraIntO : Algebra ℤ_[p] ↥(intO ↥C.S) :=
  ((algebraMap ℤ_[p] ↥C.S).codRestrict (intO ↥C.S) fun x => (norm_padicEmb C x).trans_le x.2).toAlgebra

instance padicIntTower : IsScalarTower ℤ_[p] ↥(intO ↥C.S) ↥C.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

end Field

section Roots

variable {p : ℕ} [Fact p.Prime] {F : IntermediateField ℚ ℂ} {C : Type} [Field C] [IsAlgClosed C]

theorem exists_eps_of_hom (f : F →+* C) : ∃ ε : Eps p C, ∀ (n : ℕ) (h : zeta (p ^ n) ∈ F),
    (ε.1.lev n : C) = f ⟨zeta (p ^ n), h⟩ := by
  have hp : p.Prime := Fact.out
  letI : Algebra F C := f.toAlgebra
  have key : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra K C],
      Nonempty (algebraicClosure K L →ₐ[K] C) := fun _ _ _ _ _ _ => ⟨IsAlgClosed.lift⟩
  obtain ⟨g⟩ := key F ℂ
  have hz : ∀ n, IsPrimitiveRoot (zeta (p ^ n)) (p ^ n) := fun n =>
    Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hp.ne_zero)
  have hm : ∀ n, zeta (p ^ n) ∈ algebraicClosure F ℂ := fun n =>
    mem_algebraicClosure_iff'.2 ((hz n).isIntegral (pow_pos hp.pos n)).tower_top
  have hz' : ∀ n, IsPrimitiveRoot (g ⟨_, hm n⟩) (p ^ n) := fun n =>
    (IsPrimitiveRoot.of_map_of_injective (f := (algebraicClosure F ℂ).val) (hz n)
      Subtype.val_injective).map_of_injective g.injective
  let s : ℕ → Cˣ := fun n => ((hz' n).isUnit (pow_ne_zero _ hp.ne_zero)).unit
  have hs : ∀ n, (s n : C) = g ⟨_, hm n⟩ := fun _ => rfl
  refine ⟨⟨Tate.mk s fun n => ⟨Units.ext (hz' n).pow_eq_one, Units.ext ?_⟩, ?_⟩, fun n h => g.commutes ⟨_, h⟩⟩
  · rw [Units.val_pow_eq_pow_val, hs, hs, ← map_pow]
    refine congrArg g (Subtype.ext ?_)
    have h0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    change zeta (p ^ (n + 1)) ^ p = zeta (p ^ n)
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    ring
  · exact IsPrimitiveRoot.coe_units_iff.1 ((congrArg (IsPrimitiveRoot (g ⟨_, hm 1⟩)) (pow_one p)).mp (hz' 1))

end Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p}

def objAct {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj Dw l b s) :
    letI := H.starRing; (Obj.toPolAV o).OAct (𝓞 E) :=
  letI := H.starRing
  { toRingAct := o.t.act.toRingAct, rosati := SAB.rosatiAdj o.t }

section Fibre

variable (P : PointsOfFlagModel.PtC Y C)

def abVar : PolAV (Sp ↥C.S) := StrictPull.polPull (Obj.toPolAV Y.oF) P.y

def abVarι : (abVar P).A.left ⟶ Y.oF.t.G.left := pullback.fst Y.oF.t.G.hom P.y

theorem isGrpPullback_abVarι : IsGrpPullback (abVar P).A Y.oF.t.G P.y (abVarι P) := isGrpPullback_pullback _ _

def abAct : letI := H.starRing; (abVar P).OAct (𝓞 E) :=
  letI := H.starRing
  (exists_oAct_polPull P.y _ (objAct Y.oF)).choose

theorem abAct_ι (a : 𝓞 E) : letI := H.starRing
    ((abAct P).act a).left ≫ abVarι P = abVarι P ≫ (Y.oF.t.act.act a).left :=
  letI := H.starRing
  (exists_oAct_polPull P.y _ (objAct Y.oF)).choose_spec a

def embAt (τ : E →+* ℂ) : E →+* ↥C.S := P.fK.comp (embF c τ)

def embInt (τ : E →+* ℂ) : 𝓞 E →+* ↥(intO ↥C.S) := embO (integers_intO C) (embAt P τ)

theorem coe_embInt (τ : E →+* ℂ) (a : 𝓞 E) : (embInt P τ a : ↥C.S) = P.emb τ a :=
  algebraMap_embO (integers_intO C) (embAt P τ) a

theorem embAt_injective : Function.Injective (embAt P) := fun _ _ h =>
  RingHom.ext fun x => congrArg Subtype.val (P.fK.injective (RingHom.congr_fun h x))

theorem isSplitting_embInt : IsSplitting (embC ↥C.S (embInt P)) := by
  classical
  obtain ⟨b⟩ := nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
  refine isSplitting_of_isUnit_discr b ?_ (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E)).isUnit
  simpa only [embInt, RingHom.comp_apply, algebraMap_embO] using det_sq_eq_discr_of_field (embAt_injective P) b

variable [Fact p.Prime]

def epsAt : Eps p ↥C.S := (exists_eps_of_hom P.fK).choose

end Fibre

variable {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P)

theorem dat_fac : spMap ((algebraMap ↥(intO ↥C.S) ↥C.S).comp A.f) ≫ A.ι = P.y ≫ Y.j := by
  rw [spMap_comp_algebraMap, Category.assoc, A.fac]
  exact P.ext

theorem isGrpPullback_abVar_model : IsGrpPullback (abVar P).A Y.t.G
    (spMap ((algebraMap ↥(intO ↥C.S) ↥C.S).comp A.f) ≫ A.ι) (abVarι P ≫ Y.m.φ) :=
  ((isGrpPullback_abVarι P).comp Y.m.cart).congr (dat_fac A).symm rfl

def abToDat : (abVar P).A.left ⟶ A.t.G.left :=
  A.m.cart.1.lift (abVarι P ≫ Y.m.φ) ((abVar P).A.hom ≫ spMap ((algebraMap ↥(intO ↥C.S) ↥C.S).comp A.f))
    (by rw [(isGrpPullback_abVar_model A).1.w, Category.assoc])

theorem abToDat_φ : abToDat A ≫ A.m.φ = abVarι P ≫ Y.m.φ := A.m.cart.1.lift_fst _ _ _

theorem abToDat_hom :
    abToDat A ≫ A.t.G.hom = (abVar P).A.hom ≫ spMap ((algebraMap ↥(intO ↥C.S) ↥C.S).comp A.f) :=
  A.m.cart.1.lift_snd _ _ _

theorem isGrpPullback_abToDat :
    IsGrpPullback (abVar P).A A.t.G (spMap ((algebraMap ↥(intO ↥C.S) ↥C.S).comp A.f)) (abToDat A) :=
  A.m.cart.cancel ((isGrpPullback_abVar_model A).congr rfl (abToDat_φ A).symm) (abToDat_hom A)

theorem abAct_abToDat (a : 𝓞 E) : letI := H.starRing
    ((abAct P).act a).left ≫ abToDat A = abToDat A ≫ (A.t.act.act a).left := by
  letI := H.starRing
  apply A.m.cart.1.hom_ext
  · have h₁ : abToDat A ≫ A.m.cm.F = abVarι P ≫ Y.m.cm.F := abToDat_φ A
    rw [Category.assoc, Category.assoc, A.m.act, h₁, reassoc_of% h₁, ← Y.m.act, reassoc_of% abAct_ι P a]
  · rw [Category.assoc, Category.assoc, Over.w, abToDat_hom, Over.w_assoc]

variable [Fact p.Prime]

theorem exists_pow_mem_span : ∃ n : ℕ, ∀ a ∈ maximalIdeal A.R ^ n, A.f a ∈ Ideal.span {(p : ↥(intO ↥C.S))} := by
  have hO := integers_intO C
  haveI := A.noeth
  haveI := NormIntegers.isLocalRing hO
  have hle : (maximalIdeal A.R).map A.f ≤ maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (NormIntegers.mem_maximalIdeal_iff hO).2 (A.f_loc a ha)
  have hp : 0 < ‖algebraMap ↥(intO ↥C.S) ↥C.S (p : ↥(intO ↥C.S))‖ := by
    rw [map_natCast]
    exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨w, hw⟩ := NormIntegers.isPrincipal_of_fg hO ((maximalIdeal A.R).fg_of_isNoetherianRing.map A.f)
  rw [Ideal.submodule_span_eq] at hw
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hp ((NormIntegers.mem_maximalIdeal_iff hO).1
    (hle (hw ▸ Ideal.mem_span_singleton_self w)))
  refine ⟨n, fun a ha => ?_⟩
  have h := Ideal.mem_map_of_mem A.f ha
  rw [Ideal.map_pow, hw, NormIntegers.mem_span_singleton_pow_iff hO] at h
  rw [Ideal.mem_span_singleton, NormIntegers.dvd_iff_norm_le hO]
  exact h.trans hn.le

def htPoint : letI := H.starRing; Point p (fldVal C) ↥(intO ↥C.S) (𝓞 E) :=
  letI := H.starRing
  ofCompletion (integers_intO C) (epsAt P) A.f (exists_pow_mem_span A) A.t.semi A.t.act.toRingAct
    (raynaud_spec A.U.U.toUnifPre).1.some (raynaudAct A.U.U.toUnifPre A.U.oD) (raynaudCmp A.U.U.toUnifPre)
    (raynaud_spec A.U.U.toUnifPre).2.2.2 (raynaudCmp_act A.U.U.toUnifPre A.U.oD A.U.lin)
    (abVar P) (abAct P) (abToDat A) (isGrpPullback_abToDat A) (abAct_abToDat A)

def htToModel : letI := H.starRing; (htPoint A).G.left ⟶ Y.t.G.left :=
  pullback.fst A.t.G.hom (spMap A.f) ≫ A.m.φ

theorem isGrpPullback_htToModel : letI := H.starRing; IsGrpPullback (htPoint A).G Y.t.G P.yt (htToModel A) :=
  ((isGrpPullback_pullback A.t.G (spMap A.f)).comp A.m.cart).congr A.fac rfl

end GlobalTheory.LocM
