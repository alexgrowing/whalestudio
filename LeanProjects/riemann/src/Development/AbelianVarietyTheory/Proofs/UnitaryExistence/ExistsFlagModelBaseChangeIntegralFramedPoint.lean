import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrierStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointEigenbasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Exist.FlagBaseChange

section Transport

open MonObj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem exists_pointEquiv (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t : T ⟶ S') (x : T ⟶ S) (hx : t ≫ f = x) :
    ∃ B : (Over.mk t ⟶ G') ≃* (Over.mk x ⟶ G), ∀ v, (B v).left = v.left ≫ φ := by
  subst hx
  have hl : ∀ v, (pushHom h (Over.mk t) v).left = v.left ≫ φ := fun v => rfl
  refine ⟨MulEquiv.ofBijective (pushHom h (Over.mk t)) ⟨fun v w e => ?_, fun w => ?_⟩, hl⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← hl, ← hl, e]
    · rw [Over.w v, Over.w w]
  · refine ⟨Over.homMk (h.1.lift w.left t (Over.w w)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    rw [hl]
    exact h.1.lift_fst _ _ _

variable {R : Type} [CommRing R]

abbrev epsAt (x : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x)

def TanAt (x : Sp R ⟶ S) (v : epsAt x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left

def EigAt {O : Type} (x : Sp R ⟶ S) (act : O → (G ⟶ G)) (χ : O → R) (v : epsAt x ⟶ G) : Prop :=
  ∀ a, (v ≫ act a).left = spMap (epsMul (χ a)) ≫ v.left

def CombAt (x : Sp R ⟶ S) {m : ℕ} (v : Fin m → (epsAt x ⟶ G)) (a : Fin m → R) (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin m → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsMul (a i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

theorem epsMul_over (a : R) :
    spMap (epsMul a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  rw [GlobalTheory.EtaVal.spMap_comp_spMap]
  congr 1
  ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_over :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [GlobalTheory.EtaVal.spMap_comp_spMap]
  have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext s; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]
  exact Spec.map_id _

theorem exists_tangentEquiv (h : IsGrpPullback G' G f φ) {O : Type} (act' : O → (G' ⟶ G')) (act : O → (G ⟶ G))
    (hact : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) (t : Sp R ⟶ S') (x : Sp R ⟶ S) (hx : t ≫ f = x) :
    ∃ B : (epsAt t ⟶ G') ≃* (epsAt x ⟶ G), (∀ v, (B v).left = v.left ≫ φ) ∧
      (∀ v, TanAt x (B v) ↔ TanAt t v) ∧ (∀ χ v, EigAt x act χ (B v) ↔ EigAt t act' χ v) ∧
      ∀ (m : ℕ) (v : Fin m → (epsAt t ⟶ G')) a w, CombAt x (fun i => B (v i)) a (B w) ↔ CombAt t v a w := by
  obtain ⟨B, hB⟩ := exists_pointEquiv h (spMap (algebraMap R (DualNumber R)) ≫ t)
    (spMap (algebraMap R (DualNumber R)) ≫ x) (by rw [Category.assoc, hx])
  obtain ⟨A, hA⟩ := exists_pointEquiv h t x hx
  have hw : ∀ v : epsAt t ⟶ G', v.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ t := fun v => Over.w v
  have sc : ∀ (a : R) (u v : epsAt t ⟶ G'),
      (B u).left = spMap (epsMul a) ≫ (B v).left ↔ u.left = spMap (epsMul a) ≫ v.left := by
    intro a u v
    rw [hB, hB]
    refine ⟨fun e => h.1.hom_ext (by rw [e, Category.assoc]) ?_, fun e => by rw [e, Category.assoc]⟩
    rw [Category.assoc, hw, hw, ← Category.assoc, epsMul_over]
  have prod : ∀ (m : ℕ) (u : Fin m → (epsAt t ⟶ G')), B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod := by
    intro m u
    rw [map_list_prod, List.map_ofFn]
    rfl
  refine ⟨B, hB, fun v => ?_, fun χ v => ?_, fun m v a w => ?_⟩
  · unfold TanAt
    rw [← map_one A, hA, hB]
    refine ⟨fun e => h.1.hom_ext (by rw [← e, Category.assoc]) ?_, fun e => by rw [← e, Category.assoc]⟩
    rw [Category.assoc, hw, ← Category.assoc, fst_over, Category.id_comp]
    exact (Over.w (1 : Over.mk t ⟶ G')).symm
  · refine forall_congr' fun a => ?_
    have e : B v ≫ act a = B (v ≫ act' a) := by
      apply Over.OverMorphism.ext
      rw [hB, Over.comp_left, Over.comp_left, hB, Category.assoc, Category.assoc, hact]
    rw [e]
    exact sc _ _ _
  · constructor
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => B.symm (u i), fun i => (sc _ _ _).1 (by rw [B.apply_symm_apply]; exact hu i), B.injective ?_⟩
      rw [prod, e]
      simp
    · rintro ⟨u, hu, e⟩
      exact ⟨fun i => B (u i), fun i => (sc _ _ _).2 (hu i), by rw [e, prod]⟩

end Transport

section Place

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem resCh_prime : (WeightAlgebra.resCh la).Prime := by
  have := la.isMaximal
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot
  letI := Ideal.Quotient.field la.asIdeal
  exact CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) (ringChar _)

theorem resCh_mem_maximalIdeal (T : CDVR) (io : K →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) :
    ((WeightAlgebra.resCh la : ℕ) : T.V) ∈ maximalIdeal T.V := by
  have hp := resCh_prime la
  have hm : ((WeightAlgebra.resCh la : ℕ) : 𝓞 K) ∈ la.asIdeal := by
    have h : ((WeightAlgebra.resCh la : ℕ) : 𝓞 K ⧸ la.asIdeal) = 0 := by
      unfold WeightAlgebra.resCh
      exact CharP.cast_eq_zero _ _
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa using h)
  have h0 : ((WeightAlgebra.resCh la : ℕ) : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : la.valuation K ((WeightAlgebra.resCh la : ℕ) : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) _).2 hm
    simpa using this
  have h2 : WithZero.log (la.valuation K ((WeightAlgebra.resCh la : ℕ) : K)) < 0 := by
    have := (WithZero.log_lt_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 h1
    simpa using this
  have h3 := ho.2 ((WeightAlgebra.resCh la : ℕ) : K)
  have h4 : 0 < vV T.V (io ((WeightAlgebra.resCh la : ℕ) : K)) := by
    rw [h3]
    exact mul_pos (by exact_mod_cast ho.1) (by unfold vLa; omega)
  have h5 : valV T.V (io ((WeightAlgebra.resCh la : ℕ) : K)) < 1 := by
    refine (WithZero.log_lt_log (valV_ne_zero ((map_ne_zero io).2 h0)) one_ne_zero).1 ?_
    unfold vV at h4
    rw [WithZero.log_one]; omega
  rw [map_natCast, ← map_natCast (algebraMap T.V T.Fr)] at h5
  exact ((IsDiscreteValuationRing.maximalIdeal T.V).valuation_lt_one_iff_mem (K := T.Fr) _).1 h5

end Place

section Model

open MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_extension (Y : Model Xo c β) {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR)
    (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom)) :
    ∃ (b : O →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c) (ιT : Sp T.V ⟶ Y.X), (algebraMap T.V T.Fr).comp b = io.comp β ∧
      z ≫ pullback.fst _ _ = x ∧ z ≫ pullback.snd _ _ = spMap io ∧
      spMap (algebraMap T.V T.Fr) ≫ ιT = z ≫ Y.j ∧ ιT ≫ Y.s = spMap b := by
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = ReciprocityTheory.ChartRestriction.G.Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, h2⟩ := extPt Y T b z hx
  exact ⟨b, z, yt, hb, hzf, hzs, h1, h2⟩

theorem exists_flag {Y : Model Xo c β} {p : ℕ} {C : SCF p} (P : PointsOfFlagModel.PtC Y C) {L : Type} [CommRing L] [Algebra c.F L]
    (y : FrPt Xo c L) (eF : L →+* ↥C.S) (h1 : eF.comp (algebraMap c.F L) = P.fK)
    (h2 : P.y ≫ pullback.fst _ _ = spMap eF ≫ y.x) :
    ∃ F : P.Flag, ∀ τ i, ∃ u' : Sp (DualNumber ↥C.S) ⟶ Y.oF.t.G.left,
      u' ≫ Y.m.φ = (F.u τ i).left ∧ u' ≫ Y.m0.toSABMap.φ = spMap (dualMap eF) ≫ y.u τ i := by
  letI : Algebra c.F ↥C.S := P.fK.toAlgebra
  let ψ : L →ₐ[c.F] ↥C.S := ⟨eF, fun a => DFunLike.congr_fun h1 a⟩
  obtain ⟨B0, l0, t0, e0, c0⟩ := exists_tangentEquiv Y.m0.toSABMap.cart Y.oF.t.act.act Xo.univ.t.act.act
    Y.m0.toSABMap.act P.y (spMap eF ≫ y.x) h2
  obtain ⟨B1, l1, t1, e1, c1⟩ := exists_tangentEquiv Y.m.cart Y.oF.t.act.act Y.t.act.act Y.m.act P.y P.x0 rfl
  have htan : ∀ τ i, IsTanAt (spMap eF ≫ y.x) (spMap (dualMap eF) ≫ y.u τ i) := fun τ i =>
    GlobalTheory.Frames.FramedBaseChange.tan_bc eF (y.tan τ i)
  have heig : ∀ τ i, IsEigAt c τ (spMap (dualMap eF) ≫ y.u τ i) := fun τ i =>
    GlobalTheory.Frames.FramedBaseChange.eig_bc ψ τ (y.eig τ i)
  let V : ∀ τ, Fin (Dw.mult τ) → (epsAt (spMap eF ≫ y.x) ⟶ Xo.univ.t.G) := fun τ i =>
    Over.homMk (spMap (dualMap eF) ≫ y.u τ i) (htan τ i).1
  refine ⟨⟨fun τ i => B1 (B0.symm (V τ i)), fun τ i => ?_, fun τ i => ?_, fun τ w hw he => ?_⟩, fun τ i => ?_⟩
  · refine (t1 _).2 ((t0 _).1 ?_)
    rw [B0.apply_symm_apply]
    exact (htan τ i).2
  · refine (e1 (P.emb τ) _).2 ((e0 _ _).1 ?_)
    rw [B0.apply_symm_apply]
    exact heig τ i
  · obtain ⟨w, rfl⟩ := B1.surjective w
    have hw0 := (t0 _).2 ((t1 _).1 hw)
    have he0 := (e0 _ _).2 ((e1 (P.emb τ) _).1 he)
    have key := GlobalTheory.Frames.eigenbasis_baseChange E H Dw l Xo c L ↥C.S ψ y τ (B0 w).left ⟨Over.w _, hw0⟩ he0
    refine (existsUnique_congr fun a => ?_).1 key
    refine Iff.trans ?_ (c1 _ (fun i => B0.symm (V τ i)) a w).symm
    refine Iff.trans ?_ (c0 _ _ a w)
    simp only [MulEquiv.apply_symm_apply]
    constructor
    · rintro ⟨u, hu, h⟩
      exact ⟨u, hu, Over.OverMorphism.ext h.symm⟩
    · rintro ⟨u, hu, h⟩
      exact ⟨u, hu, by rw [h]⟩
  · refine ⟨(B0.symm (V τ i)).left, (l1 _).symm, ?_⟩
    rw [← l0, B0.apply_symm_apply]
    rfl

end Model

def intRestrict (T : CDVR) {p : ℕ} {C : SCF p} (eF : T.Fr →+* ↥C.S) (h : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) :
    T.V →+* intO ↥C.S :=
  (eF.comp (algebraMap T.V T.Fr)).codRestrict (intO ↥C.S) h

theorem exists_factor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR)
    (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom)) {p : ℕ} {C : SCF p}
    (P : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (h1 : eF.comp io = P.fK) (h2 : P.y ≫ pullback.fst _ _ = spMap eF ≫ x) :
    ∃ ιT : Sp T.V ⟶ Y.X, spMap (intRestrict T eF hle) ≫ ιT = P.yt := by
  obtain ⟨b, z, ιT, hb, hzf, hzs, hj, hs⟩ := exists_extension Y hB T io e ho x hxs
  have hg : (intO ↥C.S).subtype.comp (intRestrict T eF hle) = eF.comp (algebraMap T.V T.Fr) := rfl
  have hprY : IsProper Y.s := projProper _ _ _ Y.proj
  have hy' : P.y = spMap eF ≫ z := by
    apply pullback.hom_ext
    · rw [h2, Category.assoc, hzf]
    · rw [P.y_over, Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap, h1]
  have halg : (intRestrict T eF hle).comp b = P.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have q1 := DFunLike.congr_fun P.compat a
    have q2 := DFunLike.congr_fun hb a
    have q3 := DFunLike.congr_fun h1 (β a)
    simp only [RingHom.comp_apply] at q1 q2 q3
    show eF (algebraMap T.V T.Fr (b a)) = _
    rw [q2, q3]; exact q1.symm
  refine ⟨ιT, GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_⟩
  · rw [P.ext, hy', ← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hg, ← GlobalTheory.EtaVal.spMap_comp_spMap,
      Category.assoc, hj, Category.assoc]
  · rw [P.yt_over, Category.assoc, hs, GlobalTheory.EtaVal.spMap_comp_spMap, halg]

theorem exists_lies_and_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → (∃ z, LiesOverBaseChange la Tw T io y z) ∧ ∀ z, LiesOverBaseChange la Tw T io y z → ∃ (g : T.V →+* intO ↥z.2.1.S) (ιT : Sp T.V ⟶ (Tw.Y z.1).X), Function.Injective g ∧ (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥z.2.1.S) : ↥z.2.1.S)‖ < 1) ∧ spMap g ≫ ιT = z.2.2.1.yt := by
  intro E _ _ _ H Dw l Xo c la Tw hTw T io e ho y hy
  letI := io.toAlgebra
  have hxs : y.1.x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) := y.1.x_over
  constructor
  · obtain ⟨C, eF, hle, hlt⟩ := (GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier T _ (resCh_prime la) hy (resCh_mem_maximalIdeal la T io e ho)).1
    obtain ⟨b, z, ιT, hb, hzf, hzs, hj, hs⟩ :=
      exists_extension (Tw.Y (lamOf la)) (hTw.1 (lamOf la)).1 T io e ho y.1.x hxs
    have hg : (intO ↥C.S).subtype.comp (intRestrict T eF hle) = eF.comp (algebraMap T.V T.Fr) := rfl
    let P : PointsOfFlagModel.PtC (Tw.Y (lamOf la)) C :=
      { alg := (intRestrict T eF hle).comp b
        fK := eF.comp io
        compat := by rw [← RingHom.comp_assoc, hg, RingHom.comp_assoc, hb, RingHom.comp_assoc]
        y := spMap eF ≫ z
        y_over := by rw [Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap]
        yt := spMap (intRestrict T eF hle) ≫ ιT
        yt_over := by rw [Category.assoc, hs, GlobalTheory.EtaVal.spMap_comp_spMap]
        ext := by
          rw [← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hg, ← GlobalTheory.EtaVal.spMap_comp_spMap, Category.assoc, hj,
            Category.assoc] }
    have hP : P.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x := by
      show (spMap eF ≫ z) ≫ _ = _
      rw [Category.assoc, hzf]
    obtain ⟨F, hF⟩ := exists_flag P y.1 eF rfl hP
    refine ⟨⟨lamOf la, C, P, F⟩, rfl, eF, rfl, hle, hlt, hP, fun τ i => ?_⟩
    exact hF τ i
  · intro z hz
    obtain ⟨hv, eF, h1, hle, hlt, h2, -⟩ := hz
    have hla : z.1.1 = la := congrArg Subtype.val hv
    have hB : PointsOfFlagModel.BaseAt z.1.1 (Tw.β z.1) := (hTw.1 z.1).1
    rw [hla] at hB
    obtain ⟨ιT, h⟩ := exists_factor hB T io e ho y.1.x hxs z.2.2.1 eF hle h1 h2
    exact ⟨intRestrict T eF hle, ιT,
      fun a a' h => IsFractionRing.injective T.V T.Fr (eF.injective (congrArg Subtype.val h)), hlt, h⟩

end GlobalTheory.Exist.FlagBaseChange
