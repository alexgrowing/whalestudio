import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration

noncomputable section

namespace GlobalTheory.ArcOfPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Id

variable {B : Scheme.{0}} {M : LB B} {F : Type} [Field F] {K : Type} [Fintype K] {ε : K → ℤ}

def idW (M : LB B) : LB.Iso M (M.pull (𝟙 B)) := isoPullId (Geo.Tor.idIso M) rfl

theorem toStk_unit (z : Sp F) (u : Fˣ) : toStk z u = (TauTwist.unitAt (𝟙 (Sp F)) z u).val := by
  rw [TauTwist.unitAt_apply, gm_val _ _ _ (by simp)]
  simp [toStk, unitOn]
  rfl

private theorem gw_idW_eq_gm {Y : Scheme.{0}} (f : Y ⟶ B) (y : Y) (i j : M.ι) (hi : f y ∈ M.U i)
    (hj : f y ∈ M.U j) : gw (idW M) f y i j = gm f y _ (M.g i j) := by
  rw [idW, gw_isoPullId _ _ _ _ _ _ hi hj]
  rfl

private theorem mem_wchart_of_forall_mem {Y : Scheme.{0}} {φ : K → (Y ⟶ B)} {j : K → M.ι} {y : Y}
    (h : ∀ k, φ k y ∈ M.U (j k)) : (𝟙 Y) y ∈ LB.wchart M φ j :=
  Set.mem_iInter.2 h

theorem genRel_id_iff (hM : M.IsLB) {pt pt₀ : K → (Sp F ⟶ B)} {t : LB.Gen (LB.LinComb M pt ε)} (ht : t.IsGen)
    (t₀ : LB.Gen (LB.LinComb M pt₀ ε)) (u : Fˣ) (z : Sp F) :
    GenRel (idW M) t t₀ u ↔ (∀ k, pt k = pt₀ k) ∧ ∀ j : K → M.ι, (∀ k, pt k z ∈ M.U (j k)) →
      gm (𝟙 _) z (LB.wchart M pt j) (t.s j) =
        TauTwist.unitAt (𝟙 (Sp F)) z u * gm (𝟙 _) z (LB.wchart M pt₀ j) (t₀.s j) := by
  rw [genRel_iff (idW M) t t₀ (u : F) z]
  constructor
  · rintro ⟨hpt, h⟩
    have hp : ∀ k, pt k = pt₀ k := fun k => by simpa using hpt k
    refine ⟨hp, fun j hj => ?_⟩
    obtain rfl : pt = pt₀ := funext hp
    have e := h j j (fun k => by simpa using hj k) hj
    have one : (∏ k, gw (idW M) (pt k) z (j k) (j k) ^ ε k) = 1 := by
      refine Finset.prod_eq_one fun k _ => ?_
      rw [gw_idW_eq_gm _ _ _ _ (hj k) (hj k), gm_self hM _ _ (hj k), one_zpow]
    rw [one, _root_.one_mul, toStk_unit, ← Units.val_mul] at e
    exact Units.ext e
  · rintro ⟨hp, h⟩
    obtain rfl : pt = pt₀ := funext hp
    refine ⟨fun k => Category.comp_id _, fun j j₀ hj₀ hj => ?_⟩
    have hj₀' : ∀ k, pt k z ∈ M.U (j₀ k) := fun k => by simpa using hj₀ k
    rw [gen_trans ht (𝟙 _) z (mem_wchart_of_forall_mem hj) (mem_wchart_of_forall_mem hj₀'), h j₀ hj₀', toStk_unit,
      ← Units.val_mul]
    congr 1
    have one : (∏ k, gw (idW M) (pt k) z (j₀ k) (j k) ^ ε k) * trF pt ε (𝟙 _) z j j₀ = 1 := by
      rw [trF, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [gw_idW_eq_gm _ _ _ _ (hj₀' k) (hj k), Category.id_comp, ← mul_zpow,
        gm_cocycle hM _ _ (hj₀' k) (hj k) (hj₀' k), gm_self hM _ _ (hj₀' k), one_zpow]
    rw [← _root_.mul_assoc, one, _root_.one_mul]

theorem val_of_genRel_id (hM : M.IsLB) {pt pt₀ : K → (Sp F ⟶ B)} {t : LB.Gen (LB.LinComb M pt ε)} (ht : t.IsGen)
    {t₀ : LB.Gen (LB.LinComb M pt₀ ε)} {u : Fˣ} (h : GenRel (idW M) t t₀ u) (z : Sp F) {J} (hJ : Good M z J) :
    val t (𝟙 _) z J = TauTwist.unitAt (𝟙 (Sp F)) z u * val t₀ (𝟙 _) z J := by
  obtain ⟨hp, h'⟩ := (genRel_id_iff hM ht t₀ u z).1 h
  obtain rfl : pt = pt₀ := funext hp
  rw [val_of t (𝟙 _) z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t₀ (𝟙 _) z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  exact h' _ fun k => hJ (pt k)

theorem genRel_id_of_val (hM : M.IsLB) {pt : PUnit → (Sp F ⟶ B)} {ε : PUnit → ℤ} {t : LB.Gen (LB.LinComb M pt ε)}
    (ht : t.IsGen) {t₀ : LB.Gen (LB.LinComb M pt ε)} {u : Fˣ}
    (h : ∀ z J, Good M z J → val t (𝟙 _) z J = TauTwist.unitAt (𝟙 (Sp F)) z u * val t₀ (𝟙 _) z J) :
    GenRel (idW M) t t₀ u := by
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  refine (genRel_id_iff hM ht t₀ u z).2 ⟨fun _ => rfl, fun j hj => ?_⟩
  obtain ⟨J, hJ, hJj⟩ := exists_good M hM z pt j (fun a b _ => by rw [Subsingleton.elim a b]) hj
  have e := h z J hJ
  rwa [val_of t (𝟙 _) z J j (fun k => by rw [Category.id_comp, hJj]),
    val_of t₀ (𝟙 _) z J j (fun k => by rw [Category.id_comp, hJj])] at e

private theorem exists_lift_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S'} (u : T.left ⟶ G.left)
    (hu : u ≫ G.hom = T.hom ≫ f) : ∃ x : T ⟶ G', x.left ≫ φ = u :=
  ⟨Over.homMk (hp.1.lift u T.hom hu) (hp.1.lift_snd _ _ _), hp.1.lift_fst _ _ _⟩

private theorem eq_of_left_comp_eq_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S'} {x x' : T ⟶ G'}
    (h : x.left ≫ φ = x'.left ≫ φ) : x = x' :=
  Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w x']))

private theorem one_left_comp_of_isGrpPullback' {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ)
    (by show _ = T.hom ≫ f; rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
  have h := hp.2 T 1 1 e e rfl rfl
  rw [_root_.mul_one] at h
  have he : e * e = e := Over.OverMorphism.ext h
  have he1 : e = 1 := by simpa using congrArg (e⁻¹ * ·) he
  exact congrArg CommaMorphism.left he1

private theorem pow_left_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S'} {x : T ⟶ G'}
    {y : Over.mk (T.hom ≫ f) ⟶ G} (h : x.left ≫ φ = y.left) (n : ℕ) : (x ^ n).left ≫ φ = (y ^ n).left := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_comp_of_isGrpPullback' hp T
  | succ n ih => rw [pow_succ, pow_succ]; exact (hp.2 T _ _ _ _ ih.symm h.symm).symm

end Id

attribute [local instance] GlobalTheory.TorusExt.gtGroup

open GlobalTheory.ModelData.ModelTate in

theorem exists_tateIsoQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {R : Type}
    [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hA : AdmBase R I) {t : SAB H (Sp R)} (P : PELUnif I t)
    (hT : P.TorsionIso) {S : Scheme.{0}} (t₀ : SAB H S) (z : Sp (FractionRing R) ⟶ S) (ψ : P.A.A.left ⟶ t₀.G.left)
    (hψ : IsGrpPullback P.A.A t₀.G z ψ) (lb : LBIso P.A.L (t₀.PP.L.pull ψ))
    (act : letI := H.starRing; ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ = ψ ≫ (t₀.act.act a).left)
    (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C]
    (J : TateIso D C (Over.mk (jFK (R := R) C ≫ z) ⟶ t₀.G) (fun a g => g ≫ t₀.act.act a)
      (fun n g g' c => WeilIs t₀.G t₀.PP.L n g g' (unitOn c))) :
    ∃ I : TateIsoQ D P.D.toPre P.oD C, I.ζ = J.ζ ∧ ∀ k, 0 < k → ∀ v p (x : TFK (R := R) C ⟶ P.A.A),
      x.left ≫ ψ = (J.ev k v).left → P.ToA C k p x → QkPt.Equiv _ C p (I.ev k v) := by
  classical
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hC : CubeSt := hL.1.cube
  have hB : P.D.toPre.TauBimult := P.D.tau_bimult

  have hlift : ∀ n v, ∃ x : TFK (R := R) C ⟶ P.A.A, x.left ≫ ψ = (J.ev n v).left := fun n v =>
    exists_lift_of_isGrpPullback hψ _ (Over.w (J.ev n v))
  choose X hX using hlift
  have tors : ∀ n, 0 < n → ∀ v, X n v ^ n = 1 := fun n hn v =>
    eq_of_left_comp_eq_of_isGrpPullback hψ (by rw [pow_left_comp_of_isGrpPullback hψ (hX n v) n, (J.onto n hn _).2 ⟨v, rfl⟩, one_left_comp_of_isGrpPullback' hψ])
  have Xadd : ∀ n a b, X n (a + b) = X n a * X n b := fun n a b =>
    eq_of_left_comp_eq_of_isGrpPullback hψ (by rw [hX, J.add]; exact hψ.2 (TFK (R := R) C) (X n a) (X n b) (J.ev n a) (J.ev n b) (hX n a).symm (hX n b).symm)
  have Xlin : ∀ n (c : 𝓞 E) a, X n (c • a) = X n a ≫ P.oA.act c := fun n c a =>
    eq_of_left_comp_eq_of_isGrpPullback hψ (by
      rw [hX, J.lin, Over.comp_left, Over.comp_left, Category.assoc, act c, ← Category.assoc, hX])
  have Xeq : ∀ n a b, X n a = X n b ↔ J.ev n a = J.ev n b := fun n a b =>
    ⟨fun h => Over.OverMorphism.ext (by rw [← hX, ← hX, h]),
      fun h => eq_of_left_comp_eq_of_isGrpPullback hψ (by rw [hX, hX, h])⟩
  have Xtow : ∀ n m, 0 < n → 0 < m → ∀ a, X (n * m) a ^ m = X n a := fun n m hn hm a =>
    eq_of_left_comp_eq_of_isGrpPullback hψ (by rw [pow_left_comp_of_isGrpPullback hψ (hX (n * m) a) m, J.tower n m hn hm a, hX])
  have Xonto : ∀ n, 0 < n → ∀ x : TFK (R := R) C ⟶ P.A.A, x ^ n = 1 → ∃ a, X n a = x := by
    intro n hn x hx
    let y : Over.mk (jFK (R := R) C ≫ z) ⟶ t₀.G := Over.homMk (x.left ≫ ψ)
      (by show _ = (TFK (R := R) C).hom ≫ z; rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    have hy : x.left ≫ ψ = y.left := rfl
    have hyn : y ^ n = 1 := Over.OverMorphism.ext (by
      rw [← pow_left_comp_of_isGrpPullback hψ hy n, hx, one_left_comp_of_isGrpPullback' hψ])
    obtain ⟨a, ha⟩ := (J.onto n hn y).1 hyn
    exact ⟨a, eq_of_left_comp_eq_of_isGrpPullback hψ (by rw [hX, ha]; exact hy.symm)⟩

  have hpt : ∀ n, 0 < n → ∀ v, ∃ p : QkPt P.D.toPre C n, P.ToA C n p (X n v) := by
    intro n hn v
    obtain ⟨f, hf, hs, -⟩ := hT C n hn
    obtain ⟨p, hp⟩ := hs _ (tors n hn v)
    exact ⟨p, (hf p _).2 hp.symm⟩
  let ev : ∀ n, D.La → QkPt P.D.toPre C n := fun n v =>
    if hn : 0 < n then Classical.choose (hpt n hn v) else GlobalTheory.TorusExt.qkZero hB C n
  have hev : ∀ n (hn : 0 < n) v, P.ToA C n (ev n v) (X n v) := fun n hn v => by
    simp only [ev, dif_pos hn]
    exact Classical.choose_spec (hpt n hn v)
  refine ⟨⟨J.ζ, J.ζ_prim, J.ζ_pow, ev, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro n hn a b
    obtain ⟨f, hf, -, heq, hadd, -⟩ := hT C n hn
    rw [GlobalTheory.TorusExt.qkAdd_iff hB, ← heq, hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB (ev n a) (ev n b)),
      ← (hf _ _).1 (hev n hn a), ← (hf _ _).1 (hev n hn b), ← (hf _ _).1 (hev n hn (a + b)), Xadd]
  · intro n hn c a
    letI := H.starRing
    obtain ⟨f, hf, -, heq, -, hact, -⟩ := hT C n hn
    rw [GlobalTheory.TorusExt.qkAct_iff hB hG P.oD, ← heq, hact _ _ _ (GlobalTheory.TorusExt.qkAct_qkSmul hB hG P.oD c (ev n a)),
      ← (hf _ _).1 (hev n hn a), ← (hf _ _).1 (hev n hn (c • a)), Xlin]
  · intro n hn a b
    obtain ⟨f, hf, -, heq, -⟩ := hT C n hn
    have key : J.ev n a = J.ev n b ↔ J.ev n (a - b) = 1 := by
      have e := J.add n (a - b) b
      rw [sub_add_cancel] at e
      rw [e]
      constructor
      · intro h; simpa using congrArg (· * (J.ev n b)⁻¹) h
      · intro h; rw [h, _root_.one_mul]
    rw [← heq, ← (hf _ _).1 (hev n hn a), ← (hf _ _).1 (hev n hn b), Xeq, key, J.ker n hn]
    exact exists_congr fun e => sub_eq_iff_eq_add'
  · intro n hn p
    obtain ⟨f, hf, -, heq, hadd, -⟩ := hT C n hn
    let pm : ℕ → QkPt P.D.toPre C n := fun m => GlobalTheory.TorusExt.qkMk hB (m • p.y) (m • p.g)
      (by rw [smul_comm, GlobalTheory.TorusExt.qk_nsmul hB, map_nsmul])
    have hadd' : ∀ q q' : QkPt P.D.toPre C n, f (GlobalTheory.TorusExt.qkAdd hB q q') = f q * f q' := fun q q' =>
      hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB q q')
    have h0 : f (pm 0) = 1 := by
      have e : GlobalTheory.TorusExt.qkAdd hB (pm 0) (pm 0) = pm 0 :=
        GlobalTheory.TorusExt.qk_ext (by simp [pm, GlobalTheory.TorusExt.qkAdd]) (by simp [pm, GlobalTheory.TorusExt.qkAdd])
      have h := hadd' (pm 0) (pm 0)
      rw [e] at h
      simpa using congrArg (· * (f (pm 0))⁻¹) h.symm
    have hm : ∀ m, f (pm m) = f p ^ m := by
      intro m
      induction m with
      | zero => rw [h0, pow_zero]
      | succ m ih =>
        have e : GlobalTheory.TorusExt.qkAdd hB (pm m) p = pm (m + 1) :=
          GlobalTheory.TorusExt.qk_ext (by simp [pm, GlobalTheory.TorusExt.qkAdd, succ_nsmul])
            (by simp [pm, GlobalTheory.TorusExt.qkAdd, succ_nsmul])
        rw [← e, hadd', ih, pow_succ]
    have hn0 : QkPt.Equiv P.D.toPre C (pm 0) (pm n) :=
      (GlobalTheory.TorusExt.equiv_iff hB _ _).2 ⟨p.y, by simp [pm], by simp [pm, GlobalTheory.TorusExt.qk_nsmul hB]⟩
    have htors : f p ^ n = 1 := by rw [← hm, ← (heq _ _).2 hn0, h0]
    obtain ⟨a, ha⟩ := Xonto n hn (f p) htors
    exact ⟨a, (heq _ _).1 (by rw [← (hf _ _).1 (hev n hn a), ha])⟩
  · intro n m hn hm a
    obtain ⟨q, hqy, hqg⟩ := GlobalTheory.ModelData.ModelTate.exists_level_down hB n m (ev (n * m) a)
    refine ⟨q, hqy, hqg, ?_⟩
    have hnm : 0 < n * m := Nat.mul_pos hn hm
    have hl := (GlobalTheory.LevelCompat.qkToAkU_level hL R I hA P.D P.A t.G t.semi P.U C n m (n * m) hn hm rfl q
      (ev (n * m) a) (X (n * m) a)).2 hqy hqg (hev _ hnm a)
    rw [Xtow n m hn hm a] at hl
    obtain ⟨f, hf, -, heq, -⟩ := hT C n hn
    exact (heq _ _).1 (by rw [← (hf _ _).1 hl, ← (hf _ _).1 (hev n hn a)])
  · intro n hn a b
    obtain ⟨f, hf, -, -, -, -, hweil⟩ := hT C n hn
    rw [hweil, ← (hf _ _).1 (hev n hn a), ← (hf _ _).1 (hev n hn b)]
    obtain ⟨r, hr, ⟨c⟩⟩ := GlobalTheory.PolAV_exists_cubical hC P.A
    obtain ⟨w, hw⟩ := lb
    have h := GlobalTheory.WeilCube.weilIs_pull c hG P.A.isAb t₀.PP.isLB hψ w hw (k := n) (T := TFK (R := R) C)
      (T₀ := Over.mk (jFK (R := R) C ≫ z)) (𝟙 _) (by simp) (tors n hn a) (tors n hn b)
      (by rw [Category.id_comp, hX]) (by rw [Category.id_comp, hX]) (J.isom n hn a b)
    simpa using h
  · intro k hk v p x hx hp
    obtain ⟨f, hf, -, heq, -⟩ := hT C k hk
    have e : x = X k v := eq_of_left_comp_eq_of_isGrpPullback hψ (by rw [hx, hX])
    subst e
    exact (heq _ _).1 (by rw [← (hf _ _).1 hp, ← (hf _ _).1 (hev k hk v)])

private theorem toUnit_comp_pow_eq_one_of_pow_eq_one {S : Scheme.{0}} {G : Over S} [GrpObj G] (σ : 𝟙_ (Over S) ⟶ G) {k : ℕ}
    (hσ : σ ^ k = 1) (X : Over S) : (toUnit X ≫ σ) ^ k = 1 := by
  rw [← comp_pow, hσ]
  simp

theorem exists_rational_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type}
    [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hA : AdmBase R I) {t : SAB H (Sp R)} (P : PELUnif I t)
    (hT : P.TorsionIso) {S : Scheme.{0}} (t₀ : SAB H S) (z : Sp (FractionRing R) ⟶ S) (ψ : P.A.A.left ⟶ t₀.G.left)
    (hψ : IsGrpPullback P.A.A t₀.G z ψ) {k : ℕ} (hk : 0 < k)
    (rat : ∀ q : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) k, ∃ p : QkPt P.D.toPre (FractionRing R) k,
      QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p q)
    (σ : 𝟙_ (Over S) ⟶ t₀.G) (hσ : σ ^ k = 1) :
    ∃ p : QkPt P.D.toPre (FractionRing R) k, ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (q : QkPt P.D.toPre F k) (x : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p q →
      x.left ≫ ψ = jFK (R := R) F ≫ z ≫ σ.left → P.ToA F k q x := by
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hK : KerPowSt := hL.1.kerPow
  have hk1 : 1 ≤ k := hk
  have key : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ x : TFK (R := R) F ⟶ P.A.A,
      x.left ≫ ψ = jFK (R := R) F ≫ z ≫ σ.left ∧ x ^ k = 1 := by
    intro F _ _
    have hu : (toUnit (Over.mk ((TFK (R := R) F).hom ≫ z)) ≫ σ).left = jFK (R := R) F ≫ z ≫ σ.left := by
      simp
    obtain ⟨x, hx⟩ := exists_lift_of_isGrpPullback hψ (T := TFK (R := R) F) _
      (Over.w (toUnit (Over.mk ((TFK (R := R) F).hom ≫ z)) ≫ σ))
    refine ⟨x, hx.trans hu, eq_of_left_comp_eq_of_isGrpPullback hψ ?_⟩
    rw [pow_left_comp_of_isGrpPullback hψ hx k, toUnit_comp_pow_eq_one_of_pow_eq_one σ hσ, one_left_comp_of_isGrpPullback' hψ]
  have hfm : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (x₁ : TFK (R := R) (FractionRing R) ⟶ P.A.A),
      x₁.left ≫ ψ = jFK (R := R) (FractionRing R) ≫ z ≫ σ.left →
      (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x₁).left ≫ ψ = jFK (R := R) F ≫ z ≫ σ.left := by
    intro F _ _ x₁ hx₁
    rw [Over.comp_left, Category.assoc, hx₁, ← Category.assoc]
    congr 1
    exact Over.w (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F)
  obtain ⟨x₁, hx₁, -⟩ := key (FractionRing R)
  obtain ⟨x₀, hx₀, hx₀k⟩ := key (AlgebraicClosure (FractionRing R))
  obtain ⟨f₀, hf₀, hsurj, -⟩ := hT (AlgebraicClosure (FractionRing R)) k hk1
  obtain ⟨q₀, hq₀⟩ := hsurj x₀ hx₀k
  obtain ⟨p, hp⟩ := rat q₀
  have e₀ : x₀ = GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) (AlgebraicClosure (FractionRing R)) ≫ x₁ :=
    eq_of_left_comp_eq_of_isGrpPullback hψ (by rw [hx₀, hfm _ x₁ hx₁])
  have hrat : P.ToA (FractionRing R) k p x₁ :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hG hK P.U hk1 hp x₁).2 ((hf₀ q₀ _).2 (by rw [hq₀, e₀]))
  refine ⟨p, fun F _ _ _ q x hq hx => ?_⟩
  have e : x = GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x₁ :=
    eq_of_left_comp_eq_of_isGrpPullback hψ (by rw [hx, hfm F x₁ hx₁])
  subst e
  exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hG hK P.U hk1 hq x₁).1 hrat

theorem exists_root_form {O X U : Type} [CommRing O] [StarRing O] [AddCommGroup X] [Module O X] [CommGroup U] (u : U)
    (B : X → X → ℤ) (add : ∀ y x x', B y (x + x') = B y x + B y x') (symm : ∀ y x, B y x = B x y)
    (bal : ∀ (a : O) y x, B (a • y) x = B y (star a • x)) {N : ℕ} (hN : ∀ y x, (N : ℤ) ∣ B y x) :
    ∃ s : X → X → U, TauTwist.IsScalarForm O s ∧ ∀ k : ℕ, 0 < k → k ∣ N → ∀ y x, s y x ^ (N / k) = (u ^ (B y x / k))⁻¹ := by
  refine ⟨fun y x => (u ^ (B y x / (N : ℤ)))⁻¹, ⟨fun y x x' => ?_, fun y x => ?_, fun a y x => ?_⟩,
    fun k hk hkN y x => ?_⟩
  · rw [add, Int.add_ediv_of_dvd_left (hN y x), zpow_add, mul_inv]
  · rw [symm]
  · rw [bal]
  · obtain ⟨m, hm⟩ := hN y x
    obtain ⟨c, rfl⟩ := hkN
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    beta_reduce
    rw [hm, Nat.mul_div_cancel_left c hk]
    simp only [Nat.cast_mul]
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
      have e1 : (k : ℤ) * c * m / ((k : ℤ) * c) = m := Int.mul_ediv_cancel_left _ (mul_ne_zero hk0 hc0)
      have e2 : (k : ℤ) * c * m / (k : ℤ) = c * m := by
        rw [_root_.mul_assoc]; exact Int.mul_ediv_cancel_left _ hk0
      rw [e1, e2, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm]

end GlobalTheory.ArcOfPoint
