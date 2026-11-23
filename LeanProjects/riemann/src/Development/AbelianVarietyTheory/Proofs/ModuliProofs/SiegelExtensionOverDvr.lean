import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaExtend

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.ThetaObjPull

theorem pic_local {R : Type} [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨U, hU, h⟩ := locZero_base (𝟙 (Sp R)) c (IsLocalRing.closedPoint R)
  have := pull_eq_zero_of_range h (𝟙 _) fun y =>
    (IsLocalRing.specializes_closedPoint y).mem_open U.isOpen hU
  rwa [pull_id, pull_id] at this

theorem lam_push {S S' : Scheme.{0}} {A : Over S} {B : Over S'} [GrpObj A] [GrpObj B] {f : S' ⟶ S}
    {ψ : B.left ⟶ A.left} (gp : IsGrpPullback B A f ψ) (c : Pic A.left) {T : Over S'} (x y : T ⟶ B) :
    lam (pull ψ c) x y = lam c (pushHom gp T x) (pushHom gp T y) := by
  simp only [lam, ← map_mul (pushHom gp T), ← pull_comp]
  rw [← map_one (pushHom gp T)]
  rfl

theorem locZero_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)
    (h₁ : LocZero (fst T A).left (cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _))) :
    LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have h₂ := (h₁.sub (locZero_base (fst T A).left (pull x.left (cls L hL)))).sub
    (locZero_base (fst T A).left (-pull (1 : T ⟶ A).left (cls L hL)))
  convert h₂ using 1
  rw [cls_translDiff hL, lam]
  simp only [map_neg, ← pull_comp, ← Over.comp_left, MonObj.comp_one]
  abel

theorem kTriv_of_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {P : LB (A ⊗ A).left}
    (hP : P.IsLB) (e : cls P hP = lam (cls L hL) (fst A A) (snd A A))
    (h : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) :
    Out.KTriv A L := by
  intro R _ t x hx
  have h₁ := (locZero_iff _ (LB.isLB_linComb hL _ _)).1 hx
  have h₂ := locZero_lam hL x h₁
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨V, hV, H⟩ := h₂ p
  refine ⟨V, hV, ?_⟩
  let T' : Over S := Out.overRes (T := Over.mk t) V
  let i : T' ⟶ Over.mk t := Out.overResι V
  have H' := pull_eq_zero_of_range H (lift (snd A T' ≫ i) (fst A T')).left fun y => by
    have e := congrArg (fun q => q.left y) (lift_fst (snd A T' ≫ i) (fst A T'))
    show (fst (Over.mk t) A).left ((lift (snd A T' ≫ i) (fst A T')).left y) ∈ V
    refine e ▸ ?_
    exact ((snd A T').left y).2
  have := h T' (i ≫ x) ((cls_eq_zero_iff (pull_isLB hP _)).1 (by
    rw [cls_pull hP, e, pull_lam, lift_fst, lift_snd]
    rwa [pull_lam, lift_fst_assoc, lift_snd, Category.assoc] at H'))
  exact congrArg (fun q => q.left) (this.trans (MonObj.comp_one i).symm)

theorem bij_of_pairing (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {o : Type} [CommRing o]
    {k : ℕ} (b : TBase o k) (s : S ⟶ Sp o) (pt : Fin (2 * P.g) → (Out.baseOver S ⟶ P.A)) (hpt : ∀ i, pt i ^ k = 1)
    (hw : ∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitS s b.ζ ^ Out.stdSymp P.g i j))
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ P.A) (hy : y ^ k = 1) :
    ∃! c : Ix P.g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i)
      (fun i => (c i).val) = y := by
  have := P.isAb.comm
  let β : o →+* K := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have hK : (k : K) ≠ 0 := by simpa using (b.unit.map β).ne_zero
  have hk0 : k ≠ 0 := by rintro rfl; simp at hK
  have : NeZero k := ⟨hk0⟩
  obtain ⟨hu, hm, -, -⟩ := hL.weil S P k (Over.mk x)
  have hze : IsPrimitiveRoot (Units.map β.toMonoidHom b.ζ) k := IsPrimitiveRoot.coe_units_iff.1 (b.prim K β)
  have hz : IsPrimitiveRoot (unitOn (Units.map β.toMonoidHom b.ζ)) k :=
    hze.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1)
  let h : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
  have hpt' : ∀ i, (h ≫ pt i) ^ k = 1 := fun i => by rw [← MonObj.comp_pow, hpt, MonObj.comp_one]
  have inj := SympBasis.injective_of_pairing (fun a b c => Out.WeilIs P.A P.L k a b c) k hu hm (fun i => h ≫ pt i) hpt'
    _ hz fun i j => by
      have w := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h (hw i j)
      rw [map_zpow] at w
      exact ObjTheta.map_unitS s x β hβ b.ζ ▸ w
  have hcard := (hL.mulN S P k (Nat.pos_of_ne_zero hk0)).2.2.2.2 K x hK
  let F : (Fin (2 * P.g) → ZMod k) → {y : Over.mk x ⟶ P.A // y ^ k = 1} := fun c =>
    ⟨∏ i, (h ≫ pt i) ^ (c i).val, by
      rw [← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hpt', one_pow]⟩
  have hB : Function.Bijective F := by
    have : Finite {y : Over.mk x ⟶ P.A // y ^ k = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hk0)
    refine Function.Injective.bijective_of_nat_card_le (fun a b e => inj congr(($e).1)) ?_
    rw [hcard]
    simp
  obtain ⟨c, hc, hc'⟩ := hB.existsUnique ⟨y, hy⟩
  refine ⟨c, ?_, fun c' e => hc' c' (Subtype.ext ?_)⟩
  · exact List.prod_ofFn.trans congr(($hc).1)
  · exact List.prod_ofFn.symm.trans e

section Dvr

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

theorem eq_zero_of_generic (hL : Out.Laws) (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] {T : Over (Sp V)}
    [GrpObj T] (hT : IsAbelianScheme T) (c : Pic T.left)
    (h : pull (pullback.fst T.hom (spMap (algebraMap V K))) c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff hN).2 (GenericTriv.exists_gen_of_generic_fibre hL V T N K (algebraMap V K) hT hN
    (IsFractionRing.injective V K) ((cls_eq_zero_iff (pull_isLB hN _)).1 (pic_local _))
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h))

variable {A : Over (Sp V)} [GrpObj A] {B : Over (Sp K)} [GrpObj B] {ψ : B.left ⟶ A.left}

theorem exists_lift (gp : IsGrpPullback B A (spMap (algebraMap V K)) ψ) (T : Over (Sp V)) :
    ∃ (T' : Over (Sp K)) (ρ : Over.mk (T'.hom ≫ spMap (algebraMap V K)) ⟶ T),
      (∀ p : T ⟶ A, ∃ x : T' ⟶ B, pushHom gp T' x = ρ ≫ p) ∧
      ∀ c : Pic T.left, pull ρ.left c = 0 → pull (pullback.fst T.hom (spMap (algebraMap V K))) c = 0 :=
  ⟨Over.mk (pullback.snd T.hom _), Over.homMk (pullback.fst T.hom _) pullback.condition,
    fun _ => pushHom_surjective gp _ _, fun _ h => h⟩

omit [GrpObj B] in

theorem exists_extension (hL : Out.Laws) (hA : IsAbelianScheme A)
    (gp : IsPullback ψ B.hom A.hom (spMap (algebraMap V K))) (c : Pic B.left) :
    ∃ (L : LB A.left) (h : L.IsLB), pull ψ (cls L h) = c := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  have a₁ : eSec A ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hN' := pull_isLB hN gp.isoPullback.inv
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hN' (pullback.lift (eK V K A) (𝟙 _) (by
    rw [eK, Category.assoc, a₁, Category.id_comp]; exact Category.comp_id _)))).1 (pic_local _)
  obtain ⟨L, w, hw⟩ := hL.extend V K A _ (pullback.lift_fst _ _ _) _ hN' ρ hρ
  refine ⟨L.L, L.isLB, ?_⟩
  have e := congrArg (pull gp.isoPullback.hom) ((cls_eq_iff (pull_isLB L.isLB _) hN').2 ⟨w, hw⟩)
  rwa [cls_pull L.isLB, cls_pull hN, ← pull_comp, ← pull_comp, Iso.hom_inv_id, pull_id,
    gp.isoPullback_hom_fst] at e

omit [GrpObj B] in

theorem dim_of_generic (hA : IsAbelianScheme A) (gp : IsPullback ψ B.hom A.hom (spMap (algebraMap V K))) {g : ℕ}
    (hg : SmoothOfRelativeDimension g B.hom) (y : B.left) : SmoothOfRelativeDimension g A.hom := by
  have := hA.smooth
  have := hA.geomConnected
  have : ConnectedSpace (Sp V) := inferInstance
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected A.hom (ψ y)
  rw [← H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback gp hn) hg y]
  exact hn

end Dvr

section Pol

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  {A : Over (Sp V)} [GrpObj A]

theorem exists_pol (hL : Out.Laws) (hA : IsAbelianScheme A) (Q : Out.PolAV (Sp K)) {ψ : Q.A.left ⟶ A.left}
    (gp : IsGrpPullback Q.A A (spMap (algebraMap V K)) ψ) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (rel : ∀ (T : Over (Sp K)) (x y : T ⟶ Q.A),
      pull (lift (pushHom gp T x) (pushHom gp T y)).left (cls P hP) = lam (cls Q.L Q.isLB) x y)
    (ha : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
    (hk : ∀ (T : Over (Sp V)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) :
    ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧
      LBIso Q.L (L.pull ψ) := by
  have := hA.comm
  obtain ⟨L, h, e⟩ := exists_extension hL hA gp.1 (cls Q.L Q.isLB)
  have push : ∀ (T : Over (Sp K)) (x : T ⟶ Q.A),
      pull (pushHom gp T x).left (cls L h) = pull x.left (cls Q.L Q.isLB) := fun T x => by
    rw [← e, ← pull_comp]; rfl
  have e₁ : cls P hP = lam (cls L h) (fst A A) (snd A A) := by
    obtain ⟨T, ρ, hρ, H⟩ := exists_lift gp (A ⊗ A)
    obtain ⟨x, hx⟩ := hρ (fst A A)
    obtain ⟨y, hy⟩ := hρ (snd A A)
    refine sub_eq_zero.1 (eq_zero_of_generic hL K (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA) _ (H _ ?_))
    have r := rel T x y
    rw [← e, lam_push gp, hx, hy, ← comp_lift, lift_fst_snd, Category.comp_id] at r
    rw [map_sub, pull_lam, r, sub_self]
  obtain ⟨T, ρ, hρ, H⟩ := exists_lift gp A
  obtain ⟨z, hz⟩ := hρ (𝟙 A)
  rw [Category.comp_id] at hz
  subst hz
  have e₂ : pull (GrpObj.inv : A ⟶ A).left (cls L h) = cls L h := by
    refine sub_eq_zero.1 (eq_zero_of_generic hL K hA _ (H _ ?_))
    obtain ⟨U, hU, t⟩ := Q.sym (IsLocalRing.closedPoint K)
    have t₁ := (cls_eq_zero_iff (LB.isLB_linComb Q.isLB _ _)).2 t
    rw [cls_linComb Q.isLB, Fin.sum_univ_two] at t₁
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, one_smul, neg_smul, ← sub_eq_add_neg,
      ← map_sub] at t₁
    have t₂ := pull_eq_zero_of_range t₁ z.left fun y =>
      (IsLocalRing.specializes_closedPoint (Q.A.hom (z.left y))).mem_open U.isOpen hU
    rw [map_sub, ← pull_comp, ← Over.comp_left, ← Hom.inv_def, ← push, ← push, map_inv, Hom.inv_def] at t₂
    rw [map_sub, ← pull_comp, ← Over.comp_left, t₂]
  have e₃ : pull (lift (𝟙 A) (𝟙 A)).left (cls P hP) = 2 • cls L h := by
    refine sub_eq_zero.1 (eq_zero_of_generic hL K hA _ (H _ ?_))
    have t₁ := (cls_eq_zero_iff (LB.isLB_linComb Q.isLB _ _)).2 (hL.mulPull _ Q 2)
    rw [cls_linComb Q.isLB, Fin.sum_univ_two] at t₁
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, one_smul, pull_id] at t₁
    have t₂ := congrArg (pull z.left) t₁
    rw [map_add, map_neg, map_zsmul, map_zero, ← pull_comp, ← Over.comp_left, MonObj.comp_pow, Category.comp_id,
      pow_two z, add_neg_eq_zero] at t₂
    have t₃ : pull (1 : T ⟶ Q.A).left (cls Q.L Q.isLB) = 0 := by
      rw [Hom.one_def, Over.comp_left, pull_comp, pic_local (R := K) (pull η[Q.A].left _), map_zero]
    rw [map_sub, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id, rel, map_nsmul, push, lam, ← t₂, t₃]
    have key : ∀ a : Pic T.left, (4 : ℤ) • a - a - a + 0 - 2 • a = 0 := fun a => by abel
    rw [show (((2 : ℕ) : ℤ) ^ 2) = 4 by norm_num]
    exact key _
  refine ⟨L, h, (cls_eq_zero_iff (pull_isLB h _)).1 (pic_local _), fun s => ⟨⊤, trivial, ?_⟩, ?_,
    kTriv_of_lam h hP e₁ hk, (cls_eq_iff Q.isLB (pull_isLB h ψ)).1 e.symm⟩
  · refine (cls_eq_zero_iff (LB.isLB_linComb h _ _)).1 ?_
    rw [cls_linComb h, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, e₂, one_smul, neg_smul, add_neg_cancel]
  · have f : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
    refine (relAmple_finite_pow_iso _ A A (𝟙 _) L 2 two_pos hA hA h f).2.1.1
      ((relAmple_finite_pow_iso _ A A (𝟙 _) _ 2 two_pos hA hA (pull_isLB hP _) f).2.2.2 _ (isLB_lbPow h 2) ?_ ha)
    exact (cls_eq_iff (pull_isLB hP _) (isLB_lbPow h 2)).1 (e₃.trans (cls_lbPow h 2 _).symm)

theorem weilIs_of_generic (hL : Out.Laws) (P : Out.PolAV (Sp V)) (Q : Out.PolAV (Sp K)) {ψ : Q.A.left ⟶ P.A.left}
    (gp : IsGrpPullback Q.A P.A (spMap (algebraMap V K)) ψ) (i : LBIso Q.L (P.L.pull ψ)) {k : ℕ}
    {x y : Out.baseOver (Sp V) ⟶ P.A} (hx : x ^ k = 1) (hy : y ^ k = 1) {x' y' : Out.baseOver (Sp K) ⟶ Q.A}
    (ex : x'.left ≫ ψ = spMap (algebraMap V K) ≫ x.left) (ey : y'.left ≫ ψ = spMap (algebraMap V K) ≫ y.left)
    (c : Γ(Sp V, ⊤)ˣ)
    (h : Out.WeilIs Q.A Q.L k x' y' (Units.map (spMap (algebraMap V K)).appTop.hom.toMonoidHom c)) :
    Out.WeilIs P.A P.L k x y c := by
  have := P.isAb.comm
  obtain ⟨d, hd, -⟩ := (hL.weil _ P k (Out.baseOver (Sp V))).1 x y hx hy
  have h₁ := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (toBase (spMap (algebraMap V K))) hd
  have h₂ := (weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ P.isLB Q.isLB gp i (Out.baseOver (Sp K)) k x' y'
    (toBase _ ≫ x) (toBase _ ≫ y) _ ex.symm ey.symm).1 h
  have e := congrArg Units.val (CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB h₁ h₂)
  have inj : Function.Injective (spMap (algebraMap V K)).appTop.hom := by
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V K))
    intro a b hab
    have ha := congrArg (fun q => q.hom a) n
    have hb := congrArg (fun q => q.hom b) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at ha hb
    refine (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1
      (IsFractionRing.injective V K (ha.symm.trans (Eq.trans ?_ hb)))
    exact congrArg _ hab
  have : d = c := Units.ext (inj e)
  exact this ▸ hd

end Pol

theorem exists_tObj_extension : Out.Laws → Out.Laws2 → ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (s₁ : Sp V ⟶ Sp B) (s' : Sp K ⟶ Sp o) (s₁' : Sp K ⟶ Sp B) (c : SiegPre g k ζ s₁) (c' : SiegPre g k ζ s₁') (t' : TObj g k J b s'), s' = spMap (algebraMap V K) ≫ spMap β → c.Principal → SiegPB c' c (spMap (algebraMap V K)) → TSieg bas bas' t' c' → ∃ t : TObj g k J b (spMap β), TMap t' t (spMap (algebraMap V K)) := by
  intro hL _ g k J La _ bas bas' o B _ _ b ζ V K _ _ _ _ _ _ β s₁ s' s₁' c c' t' hs ⟨ha, hk⟩ ⟨φ, φ₂, gp₀, sq, iP, hlev⟩
    ⟨e, he, iS, hpt⟩
  subst hs
  have := t'.ab.comm
  have hinv : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have gp : IsGrpPullback t'.A c.A (spMap (algebraMap V K)) (e.inv.left ≫ φ) :=
    ((isGrpPullback_of_iso e.symm).comp gp₀).congr (Category.id_comp _) rfl
  have hΛ : (abelian₂ t'.A t'.L).IsLB := LB.isLB_linComb t'.isLB _ _
  obtain ⟨L, h, hr, hsym, hamp, hK, iL⟩ := exists_pol hL c.ab t'.pol gp c.isLB (fun T x y => by
    have a₁ := (cls_eq_iff c'.isLB (pull_isLB c.isLB _)).2 iP
    have a₂ := (cls_eq_iff c'.isLB (pull_isLB hΛ _)).2 iS
    have a₃ : cls _ hΛ = lam (cls t'.L t'.isLB) (fst _ _) (snd _ _) := cls_cube_two t'.isLB _ _ hΛ
    rw [cls_pull hΛ, a₁, cls_pull c.isLB, a₃, pull_lam] at a₂
    let x' : T ⟶ t'.A := x
    let y' : T ⟶ t'.A := y
    have a₄ := congrArg (pull (lift (x' ≫ e.inv) (y' ≫ e.inv)).left) a₂
    rw [pull_lam, tensorHom_fst, tensorHom_snd, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc,
      e.inv_hom_id, Category.comp_id, Category.comp_id, ← pull_comp] at a₄
    refine Eq.trans ?_ a₄
    congr 2
    apply pullback.hom_ext
    · refine (congrArg (fun q => q.left) (lift_fst (pushHom gp T x') (pushHom gp T y'))).trans (Eq.symm ?_)
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq.1).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
      rfl
    · refine (congrArg (fun q => q.left) (lift_snd (pushHom gp T x') (pushHom gp T y'))).trans (Eq.symm ?_)
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq.2).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
      rfl) ha hk
  have hdim := dim_of_generic c.ab gp.1 t'.dim (eSec t'.A (IsLocalRing.closedPoint K))
  choose act hact hact' _ using fun j => abelianScheme_hom_extends_dedekind_of_isGrpPullback
    existsUnique_hom_extension_semiAbelian V K c.A c.A t'.A t'.A _ _ c.ab c.ab gp gp (t'.act j) (t'.hom j)
  let P : Out.PolAV (Sp V) :=
    { A := c.A, isAb := c.ab, g := g, smoothDim := hdim, L := L, isLB := h, rigid := hr, sym := hsym, ample := hamp,
      ktriv := hK }
  let pt : Fin (2 * g) → (Out.baseOver (Sp V) ⟶ c.A) := fun i => c.lev (bas'.symm (bas (Pi.single i 1)))
  have tors : ∀ i, pt i ^ k = 1 := fun i => c.lev_tors _
  have hp : ∀ i, (t'.pt i).left ≫ e.inv.left ≫ φ = spMap (algebraMap V K) ≫ (pt i).left := fun i => by
    rw [← hpt i, ← Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
    exact hlev _
  have pair : ∀ i j, Out.WeilIs c.A L k (pt i) (pt j) (unitS (spMap β) b.ζ ^ Out.stdSymp g i j) := fun i j => by
    refine weilIs_of_generic hL P t'.pol gp iL (tors i) (tors j) (hp i) (hp j) _ ?_
    have u : Units.map (spMap (algebraMap V K)).appTop.hom.toMonoidHom (unitS (spMap β) b.ζ) =
        unitS (spMap (algebraMap V K) ≫ spMap β) b.ζ := by
      apply Units.ext
      show (spMap (algebraMap V K)).appTop.hom ((spMap β).appTop.hom _) = (_ ≫ spMap β).appTop.hom _
      rw [Scheme.Hom.comp_appTop]
      rfl
    rw [map_zpow, u]
    exact t'.pairing i j
  exact ⟨{ A := c.A, ab := c.ab, dim := hdim, L := L, isLB := h, rigid := hr, sym := hsym, ample := hamp, ktriv := hK,
           pt := pt, torsion := tors, bij := bij_of_pairing hL P b (spMap β) pt tors pair, pairing := pair,
           act := act, hom := hact }, e.inv.left ≫ φ, gp, iL, hp, hact'⟩

end GlobalTheory.ThetaExtend
