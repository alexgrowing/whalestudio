import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGenericPointHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCharacterExtAndExistsOfIntegralPoints

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.EigenSplit GlobalTheory.KernelNoTorsion GlobalTheory.HodgeTateImage
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

structure Point (p : ℕ) [Fact p.Prime] {C : Type} [Field C] (v : Valuation C ℝ≥0) (O : Type)
    [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] [StarRing Λ] where
  integers : v.Integers O

  eps : Eps p C

  A : Out.PolAV (Sp C)

  oA : A.OAct Λ

  G : Over (Sp O)
  [grpG : GrpObj G]
  [commG : IsCommMonObj G]
  semi : IsSemiAbelian G

  gen : A.A.left ⟶ G.left
  gen_pull : IsGrpPullback A.A G (spMap (algebraMap O C)) gen

  oG : Out.RingAct G Λ
  gen_act : ∀ a, (oA.act a).left ≫ gen = gen ≫ (oG.act a).left

  Ext : SplitExt (Sp O)

  Gt : Over (Sp O)
  [grpGt : GrpObj Gt]
  [commGt : IsCommMonObj Gt]

  D : Ext.GtDatum Gt

  oGt : Out.RingAct Gt Λ

  cmp : ∀ (R : Type) [CommRing R] [Algebra O R], IsNilpotent (p : R) →
    ((specO O R ⟶ Gt) ≃* (specO O R ⟶ G))
  cmp_nat : ∀ (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (hR : IsNilpotent (p : R)) (hR' : IsNilpotent (p : R')) (φ : R →ₐ[O] R') (x : specO O R ⟶ Gt),
    cmp R' hR' (ptMap φ ≫ x) = ptMap φ ≫ cmp R hR x
  cmp_act : ∀ (R : Type) [CommRing R] [Algebra O R] (hR : IsNilpotent (p : R)) (a : Λ)
    (x : specO O R ⟶ Gt), cmp R hR (x ≫ oGt.act a) = cmp R hR x ≫ oG.act a

attribute [instance] Point.grpG Point.commG Point.grpGt Point.commGt

section Cotangent

variable {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj G] in
theorem mul_mem_lie (x y : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫ (x.1 * y.1) =
    toUnit (specO O O) ≫ η[G] := by
  rw [MonObj.comp_mul, x.2, y.2]
  exact mul_one _

def lieAdd (x y : LieG G) : LieG G := ⟨x.1 * y.1, mul_mem_lie x y⟩

def lieZero (G : Over (Sp O)) [GrpObj G] : LieG G := ⟨1, MonObj.comp_one _⟩

omit [IsCommMonObj G] in
theorem omega_lieAdd (f : omega G) (x y : LieG G) : f.1 (lieAdd x y) = f.1 x + f.1 y := f.2.1 x y (mul_mem_lie x y)

omit [IsCommMonObj G] in
theorem omega_lieScale (f : omega G) (c : O) (x : LieG G) :
    f.1 (AvDefs.lieScale G c x) = c * f.1 x := f.2.2 c x _

omit [IsCommMonObj G] in
theorem omega_lieZero (f : omega G) : f.1 (lieZero G) = 0 := by
  have h := omega_lieAdd f (lieZero G) (lieZero G)
  have e : lieAdd (lieZero G) (lieZero G) = lieZero G := Subtype.ext (mul_one _)
  rw [e] at h
  linear_combination -h

variable {Λ : Type} [CommRing Λ] (α : Out.RingAct G Λ)

def omegaPull (a : Λ) : omega G →ₗ[O] omega G where
  toFun f := ⟨f.1 ∘ AvDefs.lieAct G α a, fun x y h => by
      haveI := α.hom a
      exact (congrArg f.1 (Subtype.ext (MonObj.mul_comp x.1 y.1 _))).trans
        (omega_lieAdd f (AvDefs.lieAct G α a x) (AvDefs.lieAct G α a y)),
    fun c x h => (congrArg f.1 (Subtype.ext (Category.assoc _ _ _))).trans
        (omega_lieScale f c (AvDefs.lieAct G α a x))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def omegaAct [StarRing Λ] : Λ →+* Module.End O (omega G) :=
  RingHom.mk' (MonoidHom.mk (OneHom.mk (fun a => omegaPull α (star a))
      (LinearMap.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (Subtype.ext (by
        change x.1 ≫ α.act (star 1) = x.1
        rw [star_one, α.map_one, Category.comp_id])))))
      (fun a b => LinearMap.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (Subtype.ext (by
        change x.1 ≫ α.act (star (a * b)) = (x.1 ≫ α.act (star a)) ≫ α.act (star b)
        rw [star_mul, α.map_mul, Category.assoc])))))
    fun a b => LinearMap.ext fun f => Subtype.ext (funext fun x =>
      (congrArg f.1 (Subtype.ext (by
        change x.1 ≫ α.act (star (a + b)) = (x.1 ≫ α.act (star a)) * (x.1 ≫ α.act (star b))
        rw [star_add, actPts_add]))).trans
      (omega_lieAdd f (AvDefs.lieAct G α (star a) x) (AvDefs.lieAct G α (star b) x)))

theorem omegaAct_apply [StarRing Λ] (a : Λ) (f : omega G) (x : LieG G) :
    (omegaAct α a f).1 x = f.1 (AvDefs.lieAct G α (star a) x) := rfl

theorem isEig_lieAdd {τ : Λ →+* O} {x y : LieG G} (hx : AvDefs.IsEig G α τ x)
    (hy : AvDefs.IsEig G α τ y) : AvDefs.IsEig G α τ (lieAdd x y) := by
  intro a
  apply Subtype.ext
  have := α.hom a
  have hx' : x.1 ≫ α.act a = ptMap (dualScale (τ a)) ≫ x.1 := congrArg Subtype.val (hx a)
  have hy' : y.1 ≫ α.act a = ptMap (dualScale (τ a)) ≫ y.1 := congrArg Subtype.val (hy a)
  show (x.1 * y.1) ≫ α.act a = ptMap (dualScale (τ a)) ≫ (x.1 * y.1)
  rw [MonObj.mul_comp, hx', hy', MonObj.comp_mul]

theorem isEig_lieZero (τ : Λ →+* O) : AvDefs.IsEig G α τ (lieZero G) := by
  intro a
  apply Subtype.ext
  have := α.hom a
  show (1 : _ ⟶ G) ≫ α.act a = ptMap (dualScale (τ a)) ≫ 1
  rw [MonObj.one_comp, MonObj.comp_one]

theorem isEig_lieScale {τ : Λ →+* O} (c : O) {x : LieG G} (hx : AvDefs.IsEig G α τ x) :
    AvDefs.IsEig G α τ (AvDefs.lieScale G c x) := by
  intro a
  apply Subtype.ext
  have hx' : x.1 ≫ α.act a = ptMap (dualScale (τ a)) ≫ x.1 := congrArg Subtype.val (hx a)
  have e : (dualScale c).comp (dualScale (τ a)) = (dualScale (τ a)).comp (dualScale c) := by
    apply AlgHom.ext
    intro y
    unfold dualScale
    simp only [AlgHom.comp_apply]
    ext <;> simp only [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul] <;> ring
  show (ptMap (dualScale c) ≫ x.1) ≫ α.act a = ptMap (dualScale (τ a)) ≫ ptMap (dualScale c) ≫ x.1
  rw [Category.assoc, hx', ← Category.assoc, ← Category.assoc, GlobalTheory.TangentPow.ptMap_comp_ptMap,
    GlobalTheory.TangentPow.ptMap_comp_ptMap, e]

variable {p : ℕ} [IsAdicComplete (Ideal.span {(p : O)}) O]

omit [IsCommMonObj G] in

def dlogTv (χ : Tv G p) : omega G :=
  ⟨(existsUnique_isAl χ).choose, (existsUnique_isAl χ).choose_spec.1.1⟩

omit [IsCommMonObj G] in
theorem isAl_dlogTv (χ : Tv G p) : IsAl χ (dlogTv χ).1 := (existsUnique_isAl χ).choose_spec.1.2

omit [IsCommMonObj G] in
theorem eq_dlogTv {χ : Tv G p} {f : omega G} (h : IsAl χ f.1) : f = dlogTv χ := Subtype.ext ((existsUnique_isAl χ).choose_spec.2 f.1 ⟨f.2, h⟩)

omit [IsCommMonObj G] in
theorem dlogTv_mul {χ χ' χ'' : Tv G p} (h : ∀ n, χ''.χ n = χ.χ n * χ'.χ n) :
    dlogTv χ'' = dlogTv χ + dlogTv χ' := by
  refine (eq_dlogTv ((GlobalTheory.HodgeTateImage.isAl_iff χ'' _).2 fun x n R _ _ hR => ?_)).symm
  have h1 := (GlobalTheory.HodgeTateImage.isAl_iff χ _).1 (isAl_dlogTv χ) x n R hR
  have h2 := (GlobalTheory.HodgeTateImage.isAl_iff χ' _).1 (isAl_dlogTv χ') x n R hR
  have h3 : GlobalTheory.HodgeTateImage.unitAt χ'' hR x =
      GlobalTheory.HodgeTateImage.unitAt χ hR x * GlobalTheory.HodgeTateImage.unitAt χ' hR x := by
    unfold GlobalTheory.HodgeTateImage.unitAt
    rw [h n, MonObj.comp_mul, GlobalTheory.GmPoints.unitOf_mul, Units.val_mul]
  rw [h3, TrivSqZeroExt.snd_mul, GlobalTheory.HodgeTateImage.unitAt_fst, GlobalTheory.HodgeTateImage.unitAt_fst, ← h1, ← h2,
    one_smul, MulOpposite.op_one, one_smul, add_comm]
  exact map_add (algebraMap O R) _ _

omit [IsCommMonObj G] in

theorem map_span_dlogTv :
    (Submodule.span O (Set.range (dlogTv (G := G) (p := p)))).map (omega G).subtype = htSpan G p := by
  rw [Submodule.map_span]
  unfold htSpan
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨χ, rfl⟩, rfl⟩
    exact ⟨(dlogTv χ).2, χ, isAl_dlogTv χ⟩
  · rintro ⟨hf, χ, hχ⟩
    exact ⟨dlogTv χ, ⟨χ, rfl⟩, (congrArg Subtype.val (eq_dlogTv (f := ⟨f, hf⟩) hχ)).symm⟩

end Cotangent

namespace Point

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

section Points

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

variable (p O) in

abbrev red (m : ℕ) : O →ₐ[O] O ⧸ Ideal.span {(p : O) ^ m} := Ideal.Quotient.mkₐ O _

omit [Fact p.Prime] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem nilp (m : ℕ) : IsNilpotent (p : O ⧸ Ideal.span {(p : O) ^ m}) := ⟨m, GlobalTheory.HodgeTateImage.pow_quot m⟩

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
include P in
theorem isLocalRing : IsLocalRing O := by
  have hv := P.integers
  have : Nontrivial O := ⟨0, 1, fun h => by simpa using congrArg (algebraMap O C) h⟩
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one] at *
  have ha' := lt_of_le_of_ne (hv.map_le_one a) ha
  have hb' := lt_of_le_of_ne (hv.map_le_one b) hb
  rw [map_add]
  exact ne_of_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt ha' hb'))

omit [Fact p.Prime] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem factor_red (m : ℕ) : ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow (p : O) (Nat.le_succ m)))) ≫ ptMap (red p O (m + 1)) = ptMap (red p O m) := by
  rw [GlobalTheory.TangentPow.ptMap_comp_ptMap]
  exact congrArg (fun φ => ptMap φ) (AlgHom.ext fun _ => rfl)

include P in

theorem hom_ext_red {X : Over (Sp O)} {Q Q' : specO O O ⟶ X}
    (h : ∀ m, ptMap (red p O m) ≫ Q = ptMap (red p O m) ≫ Q') : Q = Q' := by
  have := P.isLocalRing
  have hp : ¬IsUnit (p : O) := Fact.out
  obtain ⟨Q₀, -, hQ₀⟩ := GlobalTheory.AdicPt.existsUnique_lim O O (p : O) hp inferInstance X
    (fun m => ptMap (red p O m) ≫ Q) (fun m => by
      rw [← Category.assoc, factor_red])
  exact (hQ₀ Q fun _ => rfl).trans (hQ₀ Q' fun m => (h m).symm).symm

theorem exists_toG (x : specO O O ⟶ P.Gt) : ∃ Q : specO O O ⟶ P.G,
    ∀ m, ptMap (red p O m) ≫ Q = P.cmp _ (nilp m) (ptMap (red p O m) ≫ x) := by
  have := P.isLocalRing
  have hp : ¬IsUnit (p : O) := Fact.out
  obtain ⟨Q, hQ, -⟩ := GlobalTheory.AdicPt.existsUnique_lim O O (p : O) hp inferInstance P.G
    (fun m => P.cmp _ (nilp m) (ptMap (red p O m) ≫ x)) (fun m => by
      rw [← P.cmp_nat _ _ (nilp (m + 1)) (nilp m), ← Category.assoc, factor_red])
  exact ⟨Q, hQ⟩

def toG : (specO O O ⟶ P.Gt) →* (specO O O ⟶ P.G) :=
  MonoidHom.mk' (fun x => (P.exists_toG x).choose) fun x y => P.hom_ext_red fun m => by
    rw [(P.exists_toG _).choose_spec, MonObj.comp_mul, MonObj.comp_mul, map_mul,
      (P.exists_toG _).choose_spec, (P.exists_toG _).choose_spec]

theorem red_toG (x : specO O O ⟶ P.Gt) (m : ℕ) :
    ptMap (red p O m) ≫ P.toG x = P.cmp _ (nilp m) (ptMap (red p O m) ≫ x) := (P.exists_toG x).choose_spec m

theorem toG_bijective : Function.Bijective P.toG := by
  have := P.isLocalRing
  have hp : ¬IsUnit (p : O) := Fact.out
  refine ⟨fun x y hxy => P.hom_ext_red fun m => (P.cmp _ (nilp m)).injective ?_, fun Q => ?_⟩
  · rw [← P.red_toG, ← P.red_toG, hxy]
  · obtain ⟨x, hx, -⟩ := GlobalTheory.AdicPt.existsUnique_lim O O (p : O) hp inferInstance P.Gt
      (fun m => (P.cmp _ (nilp m)).symm (ptMap (red p O m) ≫ Q)) (fun m => (P.cmp _ (nilp m)).injective (by
        rw [P.cmp_nat _ _ (nilp (m + 1)) (nilp m), MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
          ← Category.assoc, factor_red]))
    refine ⟨x, P.hom_ext_red fun m => ?_⟩
    rw [P.red_toG, hx m]
    rw [MulEquiv.apply_symm_apply]

theorem toG_act (a : Λ) (x : specO O O ⟶ P.Gt) :
    P.toG (x ≫ P.oGt.act a) = P.toG x ≫ P.oG.act a := by
  refine P.hom_ext_red fun m => ?_
  rw [P.red_toG, ← Category.assoc (ptMap _) x, P.cmp_act, ← Category.assoc, P.red_toG]

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem exists_generic : ∃ j : (specO O O ⟶ P.G) →* Pts P.A.A, Function.Injective j ∧
    ∀ Q z, z.left ≫ P.gen = spMap (algebraMap O C) ≫ Q.left ↔ z = j Q := GlobalTheory.ChTor.exists_genericPoint_hom C O P.integers.hom_inj P.G P.semi.separated P.A.A P.gen P.gen_pull

def toA : (specO O O ⟶ P.Gt) →* Pts P.A.A := P.exists_generic.choose.comp P.toG

theorem eq_toA_iff (x : specO O O ⟶ P.Gt) (z : Pts P.A.A) :
    z = P.toA x ↔ z.left ≫ P.gen = spMap (algebraMap O C) ≫ (P.toG x).left := (P.exists_generic.choose_spec.2 (P.toG x) z).symm

theorem toA_injective : Function.Injective P.toA := P.exists_generic.choose_spec.1.comp P.toG_bijective.1

theorem toA_act (a : Λ) (x : specO O O ⟶ P.Gt) :
    P.toA (x ≫ P.oGt.act a) = P.toA x ≫ P.oA.act a := by
  have h0 := (P.eq_toA_iff x (P.toA x)).1 rfl
  refine ((P.eq_toA_iff _ _).2 ?_).symm
  rw [P.toG_act, Over.comp_left, Over.comp_left, Category.assoc, P.gen_act, reassoc_of% h0]

end Points

theorem finite_flat (N : ℕ) (hN : 1 ≤ N) :
    IsFinite (torsion P.Gt N).hom ∧ Flat (torsion P.Gt N).hom := GlobalTheory.isFinite_flat_torsion_of_isGt (Sp O) P.Ext P.Gt ⟨P.D⟩ N hN
    (GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_torsion _ _ P.Ext.isAbelian N hN).1
    (GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_torsion _ _ P.Ext.isAbelian N hN).2

abbrev T : Type := TateA P.A p

def actT : Λ →+* Module.End ℤ_[p] P.T := actTate P.oA.toRingAct p _

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

def tateGt : Submodule ℤ_[p] P.T := LinearMap.range (Tate.map p P.toA)

def torusPts : (specO O O ⟶ splitTorus (Sp O) P.Ext.X) →* (specO O O ⟶ P.Gt) :=
  haveI := P.D.i_hom
  MonoidHom.mk' (fun x => x ≫ P.D.i) fun x y => MonObj.mul_comp x y _

def tateTorus : Submodule ℤ_[p] P.T := LinearMap.range (Tate.map p (P.toA.comp P.torusPts))

theorem tateTorus_le_tateGt : P.tateTorus ≤ P.tateGt := by
  rintro _ ⟨t, rfl⟩
  exact ⟨Tate.map p P.torusPts t, Tate.ext fun n => rfl⟩

variable [IsAlgClosed C] [CharZero C]

def IsWeilChar (t : P.T) (χ : Tv P.Gt p) : Prop :=
  ∀ (n : ℕ) (w : specO O O ⟶ torsion P.Gt (p ^ n)), algebraMap O C (unitOf (w ≫ χ.χ n) : O) =
    (weil P.A (p ^ n) (P.toA (w ≫ torsion.ι P.Gt (p ^ n))) (t.lev n) : C)

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem char_ext {n : ℕ} {f f' : torsion P.Gt (p ^ n) ⟶ Gm (Sp O)}
    (h : ∀ w : specO O O ⟶ torsion P.Gt (p ^ n),
      algebraMap O C (unitOf (w ≫ f) : O) = algebraMap O C (unitOf (w ≫ f') : O)) : f = f' := by
  obtain ⟨hff, hfn⟩ := P.finite_flat (p ^ n) (one_le_ppow p n)
  refine (GlobalTheory.torsionCharacter_ext_and_exists_of_integral_points C v O P.integers P.Gt (p ^ n)
    (one_le_ppow p n) hff hfn).1 f f' fun w => ?_
  apply GlobalTheory.GmPoints.unitOf_bijective.1
  exact Units.ext (P.integers.hom_inj (h w))

omit [IsAlgClosed C] [CharZero C] in
theorem toA_pow {N : ℕ} (w : specO O O ⟶ torsion P.Gt N) :
    P.toA (w ≫ torsion.ι P.Gt N) ^ N = 1 := by
  rw [← map_pow, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, map_one]

theorem existsUnique_isWeilChar (t : P.T) : ∃! χ : Tv P.Gt p, P.IsWeilChar t χ := by
  have hN : ∀ n, 1 ≤ p ^ n := one_le_ppow p
  have hk : ∀ n, ∃ f : torsion P.Gt (p ^ n) ⟶ Gm (Spec (CommRingCat.of O)), IsCharTors P.Gt (p ^ n) f ∧
      ∀ w : specO O O ⟶ torsion P.Gt (p ^ n), algebraMap O C (unitOf (w ≫ f) : O) =
        (weil P.A (p ^ n) (P.toA (w ≫ torsion.ι P.Gt (p ^ n))) (t.lev n) : C) := fun n =>
    (GlobalTheory.torsionCharacter_ext_and_exists_of_integral_points C v O P.integers P.Gt (p ^ n) (hN n)
      (P.finite_flat (p ^ n) (hN n)).1 (P.finite_flat (p ^ n) (hN n)).2).2
      (fun x => weil P.A (p ^ n) (P.toA x) (t.lev n)) fun x y hx hy => by
        rw [map_mul]
        exact weil_mul_left (hN n) (by rw [← map_pow, hx, map_one]) (by rw [← map_pow, hy, map_one])
          (t.lev_pow n)
  choose f hf hfw using hk
  refine ⟨⟨f, hf, fun n T x y hxy => ?_⟩, fun n w => hfw n w, fun χ hχ => ?_⟩
  · have hpow : torsion.ι P.Gt (p ^ n) ^ (p ^ (n + 1)) = 1 := by
      rw [pow_succ, pow_mul, torsionι_pow, one_pow]
    have hi : torsionLift (torsion.ι P.Gt (p ^ n)) hpow ≫ torsion.ι P.Gt (p ^ (n + 1)) =
        torsion.ι P.Gt (p ^ n) := pullback.lift_fst _ _ _
    have hy : y = x ≫ torsionLift (torsion.ι P.Gt (p ^ n)) hpow :=
      pullback.hom_ext (show y ≫ torsion.ι P.Gt (p ^ (n + 1)) =
          (x ≫ torsionLift (torsion.ι P.Gt (p ^ n)) hpow) ≫ torsion.ι P.Gt (p ^ (n + 1)) by
        rw [Category.assoc, hi, hxy]) (toUnit_unique _ _)
    rw [hy, Category.assoc]
    congr 1
    apply P.char_ext
    intro w
    rw [← Category.assoc w, hfw, hfw, Category.assoc, hi]
    have hl := weil_level (hN n) (Fact.out : p.Prime).one_lt.le (P.toA_pow w) (s := t.lev (n + 1))
      (by rw [← pow_succ]; exact t.lev_pow (n + 1))
    rw [← pow_succ] at hl
    rw [hl, t.lev_succ]
  · obtain ⟨g, hg, hgc⟩ := χ
    have : g = f := funext fun n => P.char_ext fun w => (hχ n w).trans (hfw n w).symm
    subst this
    rfl

def weilChar (t : P.T) : Tv P.Gt p := (P.existsUnique_isWeilChar t).choose

theorem isWeilChar_weilChar (t : P.T) : P.IsWeilChar t (P.weilChar t) := (P.existsUnique_isWeilChar t).choose_spec.1

theorem weilChar_add (s t : P.T) (n : ℕ) :
    (P.weilChar (s + t)).χ n = (P.weilChar s).χ n * (P.weilChar t).χ n := by
  apply P.char_ext
  intro w
  rw [MonObj.comp_mul, GlobalTheory.GmPoints.unitOf_mul, Units.val_mul, map_mul, P.isWeilChar_weilChar (s + t) n w,
    P.isWeilChar_weilChar s n w, P.isWeilChar_weilChar t n w, Tate.lev_add,
    weil_mul_right (one_le_ppow p n) (s.lev_pow n) (t.lev_pow n) (P.toA_pow w), Units.val_mul]

theorem dlogTv_weilChar_act (a : Λ) (t : P.T) :
    dlogTv (P.weilChar (P.actT a t)) = omegaAct P.oGt a (dlogTv (P.weilChar t)) := by
  have := P.oGt.hom (star a)
  have hχ : ∀ n, (P.weilChar (P.actT a t)).χ n =
      GlobalTheory.ExtensionTorsion.torsionHom (P.oGt.act (star a)) (p ^ n) ≫ (P.weilChar t).χ n := by
    intro n
    apply P.char_ext
    intro w
    rw [P.isWeilChar_weilChar (P.actT a t) n w, ← Category.assoc,
      P.isWeilChar_weilChar t n (w ≫ GlobalTheory.ExtensionTorsion.torsionHom (P.oGt.act (star a)) (p ^ n)),
      Category.assoc, GlobalTheory.ExtensionTorsion.torsionHom_ι, ← Category.assoc, P.toA_act,
      weil_act P.oA (one_le_ppow p n) (star a) (P.toA_pow w) (t.lev_pow n), star_star]
    rfl
  refine (eq_dlogTv ((GlobalTheory.HodgeTateImage.isAl_iff _ _).2 fun x n R _ _ hR => ?_)).symm
  rw [omegaAct_apply, (GlobalTheory.HodgeTateImage.isAl_iff _ _).1 (isAl_dlogTv (P.weilChar t)) _ n R hR]
  have hl : GlobalTheory.HodgeTateImage.lift hR x ≫ GlobalTheory.ExtensionTorsion.torsionHom (P.oGt.act (star a)) (p ^ n) =
      GlobalTheory.HodgeTateImage.lift hR (AvDefs.lieAct P.Gt P.oGt (star a) x) := by
    apply GlobalTheory.HodgeTateImage.eq_lift
    rw [Category.assoc, GlobalTheory.ExtensionTorsion.torsionHom_ι, ← Category.assoc, GlobalTheory.HodgeTateImage.lift_ι]
    unfold GlobalTheory.HodgeTateImage.bc
    rw [Category.assoc]
    rfl
  unfold GlobalTheory.HodgeTateImage.unitAt
  rw [hχ n, ← Category.assoc, hl]

variable [Algebra ℤ_[p] O]

def al₀ : P.T →ₗ[ℤ_[p]] omega P.Gt where
  toFun t := dlogTv (P.weilChar t)
  map_add' s t := dlogTv_mul (P.weilChar_add s t)
  map_smul' a t := Subtype.ext (funext fun x => Tate.map_smul_of_isHausdorff
    (AddMonoidHom.mk' (fun t : P.T => (dlogTv (P.weilChar t)).1 x) fun s t => by
      rw [dlogTv_mul (P.weilChar_add s t)]; rfl) a t)

theorem eq_al₀_iff (t : P.T) (f : omega P.Gt) :
    f = P.al₀ t ↔ ∃ χ : Tv P.Gt p, P.IsWeilChar t χ ∧ IsAl χ f.1 := by
  constructor
  · rintro rfl
    exact ⟨P.weilChar t, P.isWeilChar_weilChar t, isAl_dlogTv _⟩
  · rintro ⟨χ, hχ, hf⟩
    rw [(P.existsUnique_isWeilChar t).unique hχ (P.isWeilChar_weilChar t)] at hf
    exact eq_dlogTv hf

theorem al₀_act (a : Λ) (t : P.T) : P.al₀ (P.actT a t) = omegaAct P.oGt a (P.al₀ t) := P.dlogTv_weilChar_act a t

def al : O ⊗[ℤ_[p]] P.T →ₗ[O] omega P.Gt := P.al₀.liftBaseChange O

theorem al_tmul (c : O) (t : P.T) : P.al (c ⊗ₜ t) = c • P.al₀ t := rfl

theorem map_range_al_le : (LinearMap.range P.al).map (omega P.Gt).subtype ≤ htSpan P.Gt p := by
  rw [← map_span_dlogTv]
  apply Submodule.map_mono
  rintro _ ⟨u, rfl⟩
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul c t =>
    rw [P.al_tmul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨P.weilChar t, rfl⟩)
  | add u u' hu hu' =>
    rw [map_add]
    exact Submodule.add_mem _ hu hu'

end Point

end GlobalTheory.HTLat
