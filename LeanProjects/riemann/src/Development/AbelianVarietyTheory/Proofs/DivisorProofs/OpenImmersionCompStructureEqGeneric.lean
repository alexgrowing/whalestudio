import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrPtOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulipointLiftToFinerLevelCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPart
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalToGlobal.ProjectiveLattices.ExtPtUnique

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open GlobalTheory.FlatDenom

noncomputable section

namespace GlobalTheory.FlatDenom.Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'}
  (Y : Model Xo' c' (algebraMap (𝓞 c'.F) c'.F)) (r : Xo'.XF c' ⟶ Xo.XF c)
  (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))

def IsCoord {R : Type} [CommRing R] (ξ : Sp R ⟶ Y.X) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)) (U : Matrix (Fin g) (Fin g) R) {k : Type} [CommRing k]
    [Algebra c.F k] (φ : R →+* k) (yy : Sp k ⟶ Xo'.XF c') (y : FrPt Xo c k) (σ : E →+* ℂ)
    (M : Matrix (Fin (Dw.mult σ)) (Fin g) k) (C : Matrix (Fin g) (Fin (Dw.mult σ)) k) : Prop :=
  (∀ i, ∃ w : Sp (DualNumber k) ⟶ Y.oF.t.G.left,
    w ≫ Y.oF.t.G.hom = spMap (algebraMap k (DualNumber k)) ≫ yy ∧ w ≫ ν.φ = y.u σ i ∧
      IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (M i) (w ≫ Y.m.φ)) ∧
  C * M = U.map φ ∧ M * C = ((discr E : ℤ) : k) • (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) k)

omit Y ν in

theorem fst_eq {k : Type} [CommRing k] [Algebra c.F k] {yy : Sp k ⟶ Xo'.XF c'} {y : FrPt Xo c k}
    (h : yy ≫ r = GlobalTheory.AllWt.ptF y) : yy ≫ r ≫ pullback.fst _ _ = y.x := by
  rw [← Category.assoc, h]
  exact pullback.lift_fst _ _ _

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem eq_of_spMap_eq {A B : Type} [CommRing A] [CommRing B] {φ ψ : A →+* B} (h : spMap φ = spMap ψ) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem openImmersion_comp_structure_eq_generic : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c'.F) c'.F) := by
  show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
  rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]

def inclO (hle : c.F ≤ c'.F) : 𝓞 c.F →+* 𝓞 c'.F :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion hle).toRingHom

omit ν in

theorem comp_eq_of_lift {hle : c.F ≤ c'.F} (hr : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫
      spMap (IntermediateField.inclusion hle).toRingHom) {R : Type} [CommRing R] {ξ : Sp R ⟶ Y.X}
    {b : 𝓞 c'.F →+* R} (hb : ξ ≫ Y.s = spMap b) {k : Type} [CommRing k] [Algebra c.F k] {φ : R →+* k}
    {yy : Sp k ⟶ Xo'.XF c'} {y : FrPt Xo c k} (h : yy ≫ Y.j = spMap φ ≫ ξ) (h' : yy ≫ r = GlobalTheory.AllWt.ptF y) :
    ∃ io : c'.F →+* k, φ.comp b = io.comp (algebraMap (𝓞 c'.F) c'.F) ∧
      φ.comp (b.comp (inclO hle)) = (algebraMap c.F k).comp (algebraMap (𝓞 c.F) c.F) := by
  obtain ⟨io, hio⟩ : ∃ io : c'.F →+* k, spMap io = yy ≫ pullback.snd _ _ :=
    ⟨(Spec.preimage (yy ≫ pullback.snd _ _)).hom, by simp [spMap]⟩
  have e1 : φ.comp b = io.comp (algebraMap (𝓞 c'.F) c'.F) := eq_of_spMap_eq (by
    rw [← spMap_comp_eq, ← spMap_comp_eq, hio, ← hb, ← Category.assoc, ← h, Category.assoc, openImmersion_comp_structure_eq_generic, Category.assoc])
  have e2 : algebraMap c.F k = io.comp (IntermediateField.inclusion hle).toRingHom := eq_of_spMap_eq (by
    rw [← spMap_comp_eq, hio, Category.assoc, ← hr, ← Category.assoc, h', GlobalTheory.AllWt.ptF, pullback.lift_snd])
  refine ⟨io, e1, ?_⟩
  rw [← RingHom.comp_assoc, e1, e2]
  rfl

open GlobalTheory.LocM.BaseMdl in
set_option maxHeartbeats 1000000 in

theorem exists_isCoord {R : Type} [CommRing R] {ξ : Sp R ⟶ Y.X} {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)}
    (he : IsTanBasis Y.t ξ e) (σ : E →+* ℂ) {σR : 𝓞 E →+* R} {U : Matrix (Fin g) (Fin g) R}
    (hU : IsProjMat Y.t ξ σR e U) {k : Type} [CommRing k] [Algebra c.F k] {φ : R →+* k} {yy : Sp k ⟶ Xo'.XF c'}
    {y : FrPt Xo c k} (hy : yy ≫ Y.j = spMap φ ≫ ξ) (hyr : yy ≫ r = GlobalTheory.AllWt.ptF y)
    (hs : ∀ a, algebraMap c.F k (embK c σ a) = φ (σR a)) : ∃ M C, IsCoord Y r ν ξ e U φ yy y σ M C := by
  have hx : yy ≫ r ≫ pullback.fst _ _ = y.x := fst_eq r hyr
  have hy' : yy ≫ Y.jQ ≫ pullback.fst _ _ = spMap φ ≫ ξ := hy
  have hs' : (algebraMap c.F k).comp (embK c σ) = φ.comp σR := RingHom.ext hs
  have hbt : ∀ b, IsTanAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e b) := (isTanBasis_bc he φ).1
  have hut : ∀ j, IsTanAtG Xo.univ.t (yy ≫ r ≫ pullback.fst _ _) (y.u σ j) := fun j => by
    rw [hx]; exact y.tan σ j
  have hue : ∀ j, IsEigG Xo.univ.t (φ.comp σR) (y.u σ j) := fun j => hs' ▸ y.eig σ j
  have hbas : ∀ w, IsTanAtG Xo.univ.t (yy ≫ r ≫ pullback.fst _ _) w → IsEigG Xo.univ.t (φ.comp σR) w →
      ∃! a, IsCombAtG Xo.univ.t (yy ≫ r ≫ pullback.fst _ _) (y.u σ) a w := fun w h1 h2 => by
    rw [hx] at h1 ⊢
    rw [← hs'] at h2
    exact y.basis σ w h1 h2
  choose q hq1 hq2 using fun j => exists_lift ν (x' := yy) (hut j).1
  have hq1' : (fun j => q j ≫ ν.φ) = y.u σ := funext hq1
  have hqt : ∀ j, IsTanAtG Y.oF.t (yy) (q j) := fun j =>
    (tan_push ν (hq2 j)).2 (hq1 j ▸ hut j)
  have hqe : ∀ j, IsEigG Y.oF.t (φ.comp σR) (q j) := fun j =>
    (isEigG_push ν (hq2 j) _).2 (hq1 j ▸ hue j)
  have hqt' : ∀ j, IsTanAtG Y.t (spMap φ ≫ ξ) (q j ≫ Y.m.φ) := fun j => hy' ▸ (tan_push Y.m (hq2 j)).1 (hqt j)
  choose M hM using fun j => (he.2 k φ (q j ≫ Y.m.φ) (hqt' j)).exists
  have hM' : ∀ j, IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (Matrix.of M j) (q j ≫ Y.m.φ) := hM
  have hpush : ∀ {a w}, IsCombAtG Y.oF.t (yy) q a w →
      IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (Matrix.vecMul a (Matrix.of M)) (w ≫ Y.m.φ) := fun {a w} h =>
    comb_vecMul hbt hM' (hy' ▸ (comb_push Y.m hq2 a (tan_of_comb hqt h).1).1 h)
  have hC : ∀ i, ∃ a : Fin (Dw.mult σ) → k, Matrix.vecMul a (Matrix.of M) = U.map φ i := fun i => by
    obtain ⟨u, hu⟩ := exists_comb hbt (U.map φ i)
    have hut := tan_of_comb hbt hu
    obtain ⟨w, rfl, hw⟩ := exists_lift Y.m (x' := yy) (w := u) (hy' ▸ hut.1)
    have hwt : IsTanAtG Y.oF.t (yy) w := (tan_push Y.m hw).2 (hy' ▸ hut)
    have hwe : IsEigG Y.oF.t (φ.comp σR) w := (isEigG_push Y.m hw _).2 ((hU k φ).1 i _ hu)
    obtain ⟨a, ha⟩ := (hbas _ ((tan_push ν hw).1 hwt) ((isEigG_push ν hw _).1 hwe)).exists
    exact ⟨a, (he.2 k φ _ hut).unique (hpush ((comb_push ν hq2 a hw).2 (hq1' ▸ ha))) hu⟩
  choose C hC using hC
  have hCM : Matrix.of C * Matrix.of M = U.map φ := by
    ext i j
    exact congrFun (hC i) j
  have hinj : ∀ a a' : Fin (Dw.mult σ) → k, Matrix.vecMul a (Matrix.of M) = Matrix.vecMul a' (Matrix.of M) → a = a' := by
    intro a a' h
    obtain ⟨w, hw⟩ := exists_comb hqt a
    obtain ⟨w', hw'⟩ := exists_comb hqt a'
    have h1 := (tan_of_comb hqt hw).1
    have h2 := (tan_of_comb hqt hw').1
    obtain rfl : w = w' := Y.m.cart.1.hom_ext
      (GlobalTheory.FlatModel.LiftBC.isCombAtG_unique Y.t (hpush hw) (h ▸ hpush hw')) (h1.trans h2.symm)
    exact (hbas _ ((tan_push ν h1).1 (tan_of_comb hqt hw))
      ((isEigG_push ν h1 _).1 (eig_of_comb hqt hqe hw))).unique
      (hq1' ▸ (comb_push ν hq2 a h1).1 hw) (hq1' ▸ (comb_push ν hq2 a' h1).1 hw')
  refine ⟨Matrix.of M, Matrix.of C, fun i => ⟨q i, hq2 i, hq1 i, hM' i⟩, hCM, ?_⟩
  ext1 i
  refine funext_iff.1 (hinj _ _ ?_)
  have h1 := (hU k φ).2 _ _ (hM' i) ((isEigG_push Y.m (hq2 i) _).1 (hqe i))
  rw [← hCM, ← Matrix.vecMul_vecMul] at h1
  refine h1.trans ?_
  funext j
  simp [Matrix.vecMul, dotProduct, Matrix.one_apply]

omit ν in

theorem exists_lift_frPt {hle : c.F ≤ c'.F} (hr : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫
      spMap (IntermediateField.inclusion hle).toRingHom) (Z : Comp Xo c) {L : Type} [CommRing L] [IsLocalRing L]
    [Algebra c.F L] (z : Sp L ⟶ Y.X) {b : 𝓞 c'.F →+* L} (hz : z ≫ Y.s = spMap b) (hu : ∀ a, a ≠ 0 → IsUnit (b a))
    (hb : (algebraMap c.F L).comp (algebraMap (𝓞 c.F) c.F) = b.comp (inclO hle))
    (hq₀ : ∃ q, r q ∈ (Z : Set (Xo.XF c)) ∧ Y.j q = z (IsLocalRing.closedPoint L)) :
    ∃ (yy : Sp L ⟶ Xo'.XF c') (y : FrPt Xo c L), yy ≫ Y.j = z ∧ yy ≫ r = GlobalTheory.AllWt.ptF y ∧ LiesOn Z y := by
  obtain ⟨q, hqZ, hq₀⟩ := hq₀
  obtain ⟨p₀, hq, hsp⟩ : ∃ p₀ : Sp L, Y.j q = z p₀ ∧ ∀ p : Sp L, p ⤳ p₀ :=
    ⟨_, hq₀, fun p => IsLocalRing.specializes_closedPoint p⟩
  let io : c'.F →+* L := IsLocalization.lift (M := nonZeroDivisors (𝓞 c'.F)) (g := b)
    fun y => hu y (nonZeroDivisors.ne_zero y.2)
  have hio : io.comp (algebraMap (𝓞 c'.F) c'.F) = b := IsLocalization.lift_comp _
  have hio' : algebraMap c.F L = io.comp (IntermediateField.inclusion hle).toRingHom :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (by rw [hb, ← hio]; rfl)
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  let z₁ : Sp L ⟶ pullback Y.s (spMap (algebraMap (𝓞 c'.F) c'.F)) := pullback.lift z (spMap io) (by
    rw [hz, spMap_comp_eq, hio])
  have h1 : z₁ ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have h2 : Y.jQ q = z₁ p₀ := by
    apply (pullback.fst Y.s (spMap (algebraMap (𝓞 c'.F) c'.F))).isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h1]
    exact hq
  have hrg : Set.range z₁ ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    exact ((hsp p).map z₁.continuous).mem_open Y.jQ.isOpenEmbedding.isOpen_range ⟨q, h2⟩
  let yy := IsOpenImmersion.lift Y.jQ z₁ hrg
  have h3 : yy ≫ Y.jQ = z₁ := IsOpenImmersion.lift_fac _ _ _
  have h4 : (yy ≫ r) ≫ pullback.snd _ _ = spMap (algebraMap c.F L) := by
    rw [Category.assoc, hr, ← Y.jQ_over, ← Category.assoc, ← Category.assoc, h3, pullback.lift_snd, spMap_comp_eq, hio']
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt (c := c) ((yy ≫ r) ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h4, sOf, spMap_comp_eq])
  have h5 : GlobalTheory.AllWt.ptF y = yy ≫ r := by
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hy]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, h4]
  refine ⟨yy, y, ?_, h5.symm, fun p => ?_⟩
  · rw [Model.j, ← Category.assoc, h3, h1]
  · have h6 : yy p₀ = q := by
      apply Y.jQ.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h3, h2]
    rw [h5]
    refine ((hsp p).map (yy ≫ r).continuous).mem_open
      (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z).isOpen ?_
    rw [Scheme.Hom.comp_apply, h6]
    exact hqZ

include ν in
set_option maxHeartbeats 1000000 in

theorem exists_intFr_lift (T : CDVR) (io : c.F →+* T.Fr) (yt : Sp T.V ⟶ Y.X) (yy : Sp T.Fr ⟶ Xo'.XF c')
    (z : letI := io.toAlgebra; FrPt Xo c T.Fr) (hz : yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt)
    (hzr : letI := io.toAlgebra; yy ≫ r = GlobalTheory.AllWt.ptF z) :
    ∃ y₀ : IntFr Xo c T io, (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = GlobalTheory.AllWt.ptF z) := by
  letI := io.toAlgebra
  obtain ⟨G, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G Y.t yt) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', ⟨m2⟩⟩ : ∃ t' : SAB H (Sp T.Fr), Nonempty (SABMap t' G (spMap (algebraMap T.V T.Fr))) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ :=
      sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T.V T.Fr)) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨θ, hθ, -, w2, σ', ⟨g2, r2⟩, hcl, hgen⟩ :=
    GlobalTheory.DepthSum.thetaCore_trait E H Dw l' Xo' c' _ _ Y T.V yt yy hz G m t' m2
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m2
  have cancel : ∀ (p : Sp T.Fr ⟶ Y.X) (_ : p = yy ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t yy) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m3⟩ := cancel _ hz.symm n
  obtain ⟨m1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν m3
  have hx0 : yy ≫ r ≫ pullback.fst _ _ = z.x := fst_eq r hzr
  obtain ⟨y, hy⟩ := GlobalTheory.AnyLevelFrame.exists_intFr T io _ (by rw [hx0]; exact z.x_over) G t' m1 m2 θ hθ w2 σ'
    ⟨g2, r2⟩ hcl hgen
  refine ⟨y, ?_⟩
  apply pullback.hom_ext
  · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_fst, pullback.lift_fst, hy, hx0]
  · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd]

open GlobalTheory.LocM.BaseMdl in
set_option maxHeartbeats 1000000 in

theorem exists_change {R : Type} [CommRing R] {ξ : Sp R ⟶ Y.X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) {σ : E →+* ℂ}
    {U : Matrix (Fin g) (Fin g) R} {L : Type} [CommRing L] [Algebra c.F L] {φ : R →+* L} {yy : Sp L ⟶ Xo'.XF c'}
    {y : FrPt Xo c L} {M : Matrix (Fin (Dw.mult σ)) (Fin g) L} {C : Matrix (Fin g) (Fin (Dw.mult σ)) L}
    (h : IsCoord Y r ν ξ e U φ yy y σ M C) {k : Type} [Field k] [Algebra c.F k] {ι : L →ₐ[c.F] k}
    {zz : Sp k ⟶ Xo'.XF c'} {y' z : FrPt Xo c k} (hm : FrMap ι y y') (hzy : z.x = y'.x)
    (hz : zz ≫ Y.j = spMap (ι.toRingHom.comp φ) ≫ ξ) (hzr : zz ≫ r = GlobalTheory.AllWt.ptF z)
    (hpt : zz = spMap ι.toRingHom ≫ yy)
    {M' : Matrix (Fin (Dw.mult σ)) (Fin g) k} {C' : Matrix (Fin g) (Fin (Dw.mult σ)) k}
    (h' : IsCoord Y r ν ξ e U (ι.toRingHom.comp φ) zz z σ M' C') :
    ∃ a : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) k, (∀ i, IsCombAt y'.x (y'.u σ) (a i) (z.u σ i)) ∧
      M' = a * M.map ι ∧ C' * a = C.map ι := by
  have hx : zz ≫ r ≫ pullback.fst _ _ = y'.x := (fst_eq r hzr).trans hzy
  have hz' : zz ≫ Y.jQ ≫ pullback.fst _ _ = spMap (ι.toRingHom.comp φ) ≫ ξ := hz
  choose a ha using fun i => (y'.basis σ (z.u σ i) (hzy ▸ z.tan σ i) (z.eig σ i)).exists
  choose w hw1 hw2 hw3 using h.1
  choose w' hw1' hw2' hw3' using h'.1
  have hbt := (isTanBasis_bc he (ι.toRingHom.comp φ)).1
  have hq2 : ∀ j, (spMap (dualMap ι.toRingHom) ≫ w j) ≫ Y.oF.t.G.hom =
      spMap (algebraMap k (DualNumber k)) ≫ zz := fun j => by
    rw [Category.assoc, hw1, hpt, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hq1 : (fun j => (spMap (dualMap ι.toRingHom) ≫ w j) ≫ ν.φ) = y'.u σ := funext fun j => by
    rw [Category.assoc, hw2, hm.2.1]
  have hq3 : ∀ j, IsCombAtG Y.t (spMap (ι.toRingHom.comp φ) ≫ ξ) (bcV Y.t (ι.toRingHom.comp φ) e) (M.map ι j)
      ((spMap (dualMap ι.toRingHom) ≫ w j) ≫ Y.m.φ) := fun j => by
    have := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t ι.toRingHom (hw3 j)
    rw [sp_sp] at this
    rw [← bcV_bcV, Category.assoc]
    exact this
  have hM : M' = Matrix.of a * M.map ι := by
    ext1 i
    refine funext_iff.1 ?_
    have h1 : IsCombAtG Y.oF.t (zz) (fun j => spMap (dualMap ι.toRingHom) ≫ w j) (a i) (w' i) :=
      (comb_push ν hq2 (a i) (hw1' i)).2 (by rw [hq1, hw2', hx]; exact ha i)
    have h2 := comb_vecMul hbt hq3 (hz' ▸ (comb_push Y.m hq2 (a i) (hw1' i)).1 h1)
    exact (he.2 k _ _ (tan_of_comb hbt h2)).unique (hw3' i) h2
  refine ⟨Matrix.of a, ha, hM, ?_⟩
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  have hδ : ((discr E : ℤ) : k) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have e1 : C.map ι * M.map ι = U.map (ι.toRingHom.comp φ) := by
    rw [← Matrix.map_mul (f := ι), h.2.1, Matrix.map_map]; rfl
  have e2 : M.map ι * C.map ι = ((discr E : ℤ) : k) • 1 := by
    rw [← Matrix.map_mul (f := ι), h.2.2]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have e3 : C' * Matrix.of a * M.map ι = C.map ι * M.map ι := by rw [Matrix.mul_assoc, ← hM, h'.2.1, e1]
  have e4 := congrArg (· * C.map ι) e3
  simp only [Matrix.mul_assoc (C' * Matrix.of a), Matrix.mul_assoc (C.map ι), e2, Matrix.mul_smul, Matrix.mul_one] at e4
  exact smul_right_injective _ hδ e4

theorem value_map {R : Type} [CommRing R] {ξ : Sp R ⟶ Y.X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) {Z : Comp Xo c} {f : Rul Xo c}
    {σ₁ σ₂ : E →+* ℂ} (hL : DetLaw Z f σ₁ σ₂) {U₁ U₂ : Matrix (Fin g) (Fin g) R} {L : Type} [CommRing L]
    [IsLocalRing L] [Algebra c.F L] {φ : R →+* L} {yy : Sp L ⟶ Xo'.XF c'} {y : FrPt Xo c L}
    (hy : yy ≫ Y.j = spMap φ ≫ ξ) (hyr : yy ≫ r = GlobalTheory.AllWt.ptF y) (hyZ : LiesOn Z y)
    {M₁ : Matrix (Fin (Dw.mult σ₁)) (Fin g) L} {C₁ : Matrix (Fin g) (Fin (Dw.mult σ₁)) L}
    {M₂ : Matrix (Fin (Dw.mult σ₂)) (Fin g) L} {C₂ : Matrix (Fin g) (Fin (Dw.mult σ₂)) L}
    (h₁ : IsCoord Y r ν ξ e U₁ φ yy y σ₁ M₁ C₁) (h₂ : IsCoord Y r ν ξ e U₂ φ yy y σ₂ M₂ C₂)
    {k : Type} [Field k] [Algebra c.F k] (ι : L →ₐ[c.F] k) {ψ : R →+* k} (hψ : ∀ a, ψ a = ι (φ a))
    {zz : Sp k ⟶ Xo'.XF c'} {z : FrPt Xo c k} (hz : zz ≫ Y.j = spMap ψ ≫ ξ) (hzr : zz ≫ r = GlobalTheory.AllWt.ptF z)
    {M₁' : Matrix (Fin (Dw.mult σ₁)) (Fin g) k} {C₁' : Matrix (Fin g) (Fin (Dw.mult σ₁)) k}
    {M₂' : Matrix (Fin (Dw.mult σ₂)) (Fin g) k} {C₂' : Matrix (Fin g) (Fin (Dw.mult σ₂)) k}
    (h₁' : IsCoord Y r ν ξ e U₁ ψ zz z σ₁ M₁' C₁') (h₂' : IsCoord Y r ν ξ e U₂ ψ zz z σ₂ M₂' C₂')
    (I : Fin (Dw.mult σ₁) → Fin g) (J : Fin (Dw.mult σ₂) → Fin g) :
    evR Xo c f z * (M₁'.submatrix id I).det * (C₂'.submatrix J id).det =
      ι (evR Xo c f y * (M₁.submatrix id I).det * (C₂.submatrix J id).det) := by
  obtain rfl : ψ = ι.toRingHom.comp φ := RingHom.ext hψ
  obtain ⟨y', hm⟩ := GlobalTheory.FlagTan.exists_frMap ι y
  have := isPreimmersion_j Y
  have hpt : GlobalTheory.AllWt.ptF y' = spMap ι.toRingHom ≫ GlobalTheory.AllWt.ptF y := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_fst, pullback.lift_fst, hm.1]
    · rw [Category.assoc, GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd, spMap_comp_eq]
      congr 1
      exact ι.comp_algebraMap.symm
  have hzz : zz = spMap ι.toRingHom ≫ yy := by
    rw [← cancel_mono Y.j, hz, Category.assoc, hy, sp_sp]
  have hzy0 : GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF y' := by
    rw [← hzr, hzz, hpt, Category.assoc, hyr]
  have hzy : z.x = y'.x := by
    have := congrArg (· ≫ pullback.fst _ _) hzy0
    simpa only [GlobalTheory.AllWt.ptF, pullback.lift_fst] using this
  have hy'Z : LiesOn Z y' := fun s => by
    rw [hpt, Scheme.Hom.comp_apply]
    exact hyZ _
  obtain ⟨a₁, ha₁, hM₁, -⟩ := exists_change Y r ν he h₁ hm hzy hz hzr hzz h₁'
  obtain ⟨a₂, ha₂, -, hC₂⟩ := exists_change Y r ν he h₂ hm hzy hz hzr hzz h₂'
  have k1 := hL.2 k z y' hy'Z hzy a₁ a₂ ha₁ ha₂
  rw [GlobalTheory.FlagTan.evR_frMap hL.1 hm] at k1
  have k2 : (M₁'.submatrix id I).det = a₁.det * ι (M₁.submatrix id I).det := by
    rw [AlgHom.map_det, ← Matrix.det_mul, hM₁]; rfl
  have k3 : ι (C₂.submatrix J id).det = (C₂'.submatrix J id).det * a₂.det := by
    rw [AlgHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    exact (congrFun (congrFun hC₂ (J i)) j).symm
  rw [map_mul, map_mul, k2, k3]
  linear_combination (ι (M₁.submatrix id I).det * (C₂'.submatrix J id).det) * k1

open GlobalTheory.ModelFrameCompare MonObj in
set_option maxHeartbeats 1000000 in

theorem images_eigenBasis (σ : E →+* ℂ) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (xV : Sp T.V ⟶ Y.X)
    (yy : Sp T.Fr ⟶ Xo'.XF c') (hxV : yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ xV)
    (hpt : letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) :
    ∃ v : Fin (Dw.mult σ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left), (∀ j, IsTanAtG Y.t xV (v j)) ∧
      (∀ u : Sp (DualNumber T.V) ⟶ Y.t.G.left, IsTanAtG Y.t xV u →
        (∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) →
          u ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u) →
        ∃ cf : Fin (Dw.mult σ) → T.V, IsCombAtG Y.t xV v cf u) ∧
      ∀ (cf : Fin (Dw.mult σ) → T.V) (u : Sp (DualNumber T.V) ⟶ Y.t.G.left)
        (w : Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left), IsCombAtG Y.t xV v cf u →
        w ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u →
        (letI := io.toAlgebra; IsCombAt y₀.1.x (y₀.1.u σ) (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ ν.φ)) := by
  let _ := io.toAlgebra
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G Y.t xV) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull xV Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, n₀, n₂, m', -, h2⟩ := GlobalTheory.ThetaFrameCheck.genFibre_tied Xo' c' T _ _ Y xV yy hxV G₂ m
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t t₂ _ yy ν m'
  obtain ⟨G, t', m1, m2, ⟨ub, ht, he, hb, hl⟩, -⟩ := y₀.2.2
  have hx : y₀.1.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hpt]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨m1', hm1'⟩ := exists_sabMap_congr m1 hx
  obtain ⟨k, n, hk1, hk2⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr _ G G₂ t' t₂ m1' m2 n₁ n₂
  obtain ⟨nm, hnm⟩ := sabComp pullCubComp E H _ _ _ Y.t G₂ G xV (𝟙 _) m n
  obtain ⟨q₀, hq₀⟩ := exists_sabMap_congr nm (Category.id_comp xV)
  rw [hnm] at hq₀
  obtain ⟨B, hB, hBt, hBe, hBc⟩ := GlobalTheory.FactorDepth.Extension.exists_tanEquiv q₀
  refine ⟨fun j => (B (ub σ j)).left, fun j => (hBt _).2 (ht σ j), ?_, ?_⟩
  · intro u hu hue
    obtain ⟨w', hw'⟩ := B.surjective (ovT hu)
    have e : u = (B w').left := by rw [hw']; rfl
    subst e
    obtain ⟨cf, hcf, -⟩ := hb σ w' ((hBt _).1 hu) fun a z hz => (hBe _ a z).1 (hue a z hz)
    exact ⟨cf, (hBc _ _ cf w').2 hcf⟩
  · intro cf u w hc hw
    have h3 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) hc
    obtain ⟨q, hq⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t₂ _ yy Y.m m'
    choose u' hu1 hu2 using hl σ
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub σ j), spMap_comp',
        ← dualMap_comp_alg, ← spMap_comp']
      rfl
    have hov' : ∀ j, (u' j ≫ k.φ) ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
      intro j
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, hov]
    have hvec : ∀ j, spMap (dualMap (algebraMap T.V T.Fr)) ≫ (B (ub σ j)).left = (u' j ≫ k.φ) ≫ q.φ := by
      intro j
      rw [hB, hq₀, hq, ← Category.assoc, ← hu2, Category.assoc, ← Category.assoc m2.φ, hk2]
      simp only [Category.assoc, h2]
    have hpt' : spMap (algebraMap T.V T.Fr) ≫ xV = 𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _ := by
      rw [Category.id_comp, ← hxV]; rfl
    have h4 : IsCombAtG Y.t (𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _) (fun j => (u' j ≫ k.φ) ≫ q.φ)
        (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ Y.m.φ) := by
      rw [← hpt', hw]
      simpa only [hvec] using h3
    obtain ⟨w₂, hw₂, hc₂⟩ := isCombAtG_reflect q (𝟙 _) (fun j => u' j ≫ k.φ) hov' h4
    have hw₂' : w₂ ≫ m'.φ = w := by
      refine Y.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, ← hq, hw₂]
      · have := isPreimmersion_j Y
        have hmono : Mono Y.j := inferInstance
        have e2 : w₂ ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
          obtain ⟨uu, -, hh⟩ := hc₂
          rw [← hh]; exact Over.w _
        have e1 : u ≫ Y.t.G.hom = spMap (algebraMap T.V (DualNumber T.V)) ≫ xV := by
          obtain ⟨uu, -, hh⟩ := hc
          rw [← hh]; exact Over.w _
        rw [Category.assoc, m'.cart.1.w, ← Category.assoc, e2, Category.comp_id]
        apply hmono.right_cancellation
        have e3 : spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) ≫ xV =
            spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ yy ≫ Y.j := by
          rw [← Category.assoc, spMap_comp', dualMap_comp_alg, ← spMap_comp', Category.assoc, hxV]
        show (spMap _ ≫ yy) ≫ Y.j = w ≫ Y.oF.t.G.hom ≫ Y.jQ ≫ pullback.fst _ _
        rw [← Y.m.cart.1.w, ← Category.assoc w, hw, Category.assoc (spMap _) u, e1, e3, Category.assoc]
    have h5 := isCombAtG_push n₁ (𝟙 _) hc₂
    have hv5 : (fun j => (u' j ≫ k.φ) ≫ n₁.φ) = y₀.1.u σ := by
      funext j
      rw [Category.assoc, hk1, hm1', hu1]
    rw [hv5, hn₁, ← Category.assoc w₂, hw₂', Category.id_comp, ← hx] at h5
    exact h5

open GlobalTheory.LocM.BaseMdl in
set_option maxHeartbeats 1000000 in

theorem coord_integral {R : Type} [CommRing R] {ξ : Sp R ⟶ Y.X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) (σ : E →+* ℂ) {σR : 𝓞 E →+* R}
    {U : Matrix (Fin g) (Fin g) R} (hU : IsProjMat Y.t ξ σR e U) (T : CDVR) (io : c.F →+* T.Fr)
    (y₀ : IntFr Xo c T io) (φ : R →+* T.V) (yy : Sp T.Fr ⟶ Xo'.XF c')
    (hy : yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp φ) ≫ ξ)
    (hyr : letI := io.toAlgebra; yy ≫ r = GlobalTheory.AllWt.ptF y₀.1)
    (hs : ∀ a, io (embK c σ a) = algebraMap T.V T.Fr (φ (σR a)))
    (M : Matrix (Fin (Dw.mult σ)) (Fin g) T.Fr) (C : Matrix (Fin g) (Fin (Dw.mult σ)) T.Fr)
    (h : letI := io.toAlgebra; IsCoord Y r ν ξ e U ((algebraMap T.V T.Fr).comp φ) yy y₀.1 σ M C) :
    ∃ (M₀ : Matrix (Fin (Dw.mult σ)) (Fin g) T.V) (C₀ : Matrix (Fin g) (Fin (Dw.mult σ)) T.V),
      M₀.map (algebraMap T.V T.Fr) = M ∧ C₀.map (algebraMap T.V T.Fr) = C := by
  letI := io.toAlgebra
  have hinj := IsFractionRing.injective T.V T.Fr
  have hy1 : yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ spMap φ ≫ ξ := by rw [hy, sp_sp]
  have hy' : yy ≫ Y.jQ ≫ pullback.fst _ _ = spMap ((algebraMap T.V T.Fr).comp φ) ≫ ξ := hy
  have hx : yy ≫ r ≫ pullback.fst _ _ = y₀.1.x := fst_eq r hyr
  obtain ⟨v, hv1, hv2, hv3⟩ := images_eigenBasis Y r ν σ T io y₀ _ _ hy1 hyr.symm
  have hbt := (isTanBasis_bc he φ).1
  have hbt' := (isTanBasis_bc he ((algebraMap T.V T.Fr).comp φ)).1
  choose M₀ hM₀ using fun j => (he.2 T.V φ (v j) (hv1 j)).exists
  have hM₀' : ∀ j, IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (Matrix.of M₀ j) (v j) := hM₀
  choose w hw1 hw2 hw3 using h.1
  have hw2' : (fun j => w j ≫ ν.φ) = y₀.1.u σ := funext hw2

  have key : ∀ cf : Fin (Dw.mult σ) → T.V, (fun b => algebraMap T.V T.Fr (Matrix.vecMul cf (Matrix.of M₀) b)) =
      Matrix.vecMul (fun j => algebraMap T.V T.Fr (cf j)) M := fun cf => by
    obtain ⟨u, hu⟩ := exists_comb hv1 cf
    have h1 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) (comb_vecMul hbt hM₀' hu)
    rw [sp_sp] at h1
    have h2 : IsCombAtG Y.t (spMap ((algebraMap T.V T.Fr).comp φ) ≫ ξ) (bcV Y.t ((algebraMap T.V T.Fr).comp φ) e)
        (fun b => algebraMap T.V T.Fr (Matrix.vecMul cf (Matrix.of M₀) b))
        (spMap (dualMap (algebraMap T.V T.Fr)) ≫ u) := by
      rw [← bcV_bcV]; exact h1
    have h3 := tan_of_comb hbt' h2
    obtain ⟨w', hw', hw''⟩ := exists_lift Y.m (x' := yy) (hy' ▸ h3.1)
    have h4 := hv3 cf u w' hu hw'
    have h5 : IsCombAtG Y.oF.t (yy) w (fun j => algebraMap T.V T.Fr (cf j)) w' :=
      (comb_push ν hw1 _ hw'').2 (by rw [hw2', hx]; exact h4)
    have h6 := comb_vecMul hbt' hw3 (hy' ▸ (comb_push Y.m hw1 _ hw'').1 h5)
    rw [hw'] at h6
    exact (he.2 T.Fr _ _ h3).unique h2 h6
  have hM : (Matrix.of M₀).map (algebraMap T.V T.Fr) = M := by
    ext i b
    have := congrFun (key (Pi.single i 1)) b
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using this
  have hC : ∀ i, ∃ cf : Fin (Dw.mult σ) → T.V, Matrix.vecMul cf (Matrix.of M₀) = U.map φ i := fun i => by
    obtain ⟨u, hu⟩ := exists_comb hbt (U.map φ i)
    obtain ⟨cf, hcf⟩ := hv2 u (tan_of_comb hbt hu) fun a z hz => by
      rw [hinj (hz.trans (hs a))]
      exact (hU T.V φ).1 i u hu a
    exact ⟨cf, (he.2 T.V φ u (tan_of_comb hbt hu)).unique (comb_vecMul hbt hM₀' hcf) hu⟩
  choose C₀ hC₀ using hC
  refine ⟨Matrix.of M₀, Matrix.of C₀, hM, ?_⟩
  have hδ : ((discr E : ℤ) : T.Fr) ≠ 0 := by
    haveI : CharZero T.Fr := charZero_of_injective_algebraMap hinj
    exact Int.cast_ne_zero.2 (discr_ne_zero E)
  have e0 : Matrix.of C₀ * Matrix.of M₀ = U.map φ := by
    ext i j
    exact congrFun (hC₀ i) j
  have e3 : (Matrix.of C₀).map (algebraMap T.V T.Fr) * M = C * M := by
    rw [h.2.1, ← hM, ← Matrix.map_mul, e0, Matrix.map_map]; rfl
  have e4 := congrArg (· * C) e3
  simp only [Matrix.mul_assoc, h.2.2, Matrix.mul_smul, Matrix.mul_one] at e4
  exact smul_right_injective _ hδ e4

def algHomOf {K L k : Type} [Field K] [NumberField K] [CommRing L] [CommRing k] [Algebra K L] [Algebra K k]
    (ι : L →+* k) (h : ι.comp ((algebraMap K L).comp (algebraMap (𝓞 K) K)) = (algebraMap K k).comp (algebraMap (𝓞 K) K)) :
    L →ₐ[K] k :=
  { ι with
    commutes' := fun a => DFunLike.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
      (j := ι.comp (algebraMap K L)) (k := algebraMap K k) h) a }

theorem exists_algebra {K L : Type} [Field K] [NumberField K] [CommRing L] (b : 𝓞 K →+* L)
    (h : ∀ a, a ≠ 0 → IsUnit (b a)) : ∃ _ : Algebra K L, (algebraMap K L).comp (algebraMap (𝓞 K) K) = b :=
  ⟨(IsLocalization.lift (M := nonZeroDivisors (𝓞 K)) (S := K) (g := b)
    fun y => h y (nonZeroDivisors.ne_zero y.2)).toAlgebra, IsLocalization.lift_comp _⟩

theorem vV_eq_zero {K : Type} [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr) (b : 𝓞 K →+* T.V)
    (hb : ∀ a, io (algebraMap (𝓞 K) K a) = algebraMap T.V T.Fr (b a)) (hn : ∀ n : ℕ, 0 < n → IsUnit (n : T.V))
    (a : K) (ha : a ≠ 0) : vV T.V (io a) = 0 := by
  have key : ∀ x : K, io x ∈ (algebraMap T.V T.Fr).range := by
    intro x
    have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have := Algebra.IsAlgebraic.trans ℤ ℚ K
    obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple
    have hu : IsUnit ((y : ℤ) : T.V) := by
      have := hn y.natAbs (Int.natAbs_pos.2 hy0)
      rcases Int.natAbs_eq y with e | e
      · rw [e]; simpa using this
      · rw [e]; simpa using this.neg
    obtain ⟨u, hu⟩ := hu
    obtain ⟨s, hs⟩ : ∃ s : 𝓞 K, algebraMap (𝓞 K) K s = y • x := ⟨⟨y • x, hy⟩, rfl⟩
    refine ⟨(u⁻¹ : T.Vˣ) * b s, ?_⟩
    rw [map_mul, ← hb]
    have e1 : io (algebraMap (𝓞 K) K s) = algebraMap T.V T.Fr u * io x := by
      rw [hu, map_intCast, ← map_intCast io, ← map_mul, ← zsmul_eq_mul, hs]
    rw [e1, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  have nn : ∀ x : K, 0 ≤ vV T.V (io x) := fun x => by
    obtain ⟨s, hs⟩ := key x
    rw [← hs]
    by_cases h : algebraMap T.V T.Fr s = 0
    · simp [h, vV]
    have := (WithZero.log_le_log (valV_ne_zero (V := T.V) h) one_ne_zero).2
      (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ s)
    rw [WithZero.log_one] at this
    rw [vV]; omega
  have h := vV_mul (V := T.V) ((map_ne_zero io).2 ha) ((map_ne_zero io).2 (inv_ne_zero ha))
  rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h
  have := nn a
  have := nn a⁻¹
  omega

theorem inclO_ne_zero (hle : c.F ≤ c'.F) {a : 𝓞 c.F} (ha : a ≠ 0) : inclO hle a ≠ 0 := fun h => ha (by
  have h1 : IntermediateField.inclusion hle (algebraMap (𝓞 c.F) c.F a) = 0 := congrArg (algebraMap (𝓞 c'.F) c'.F) h
  exact RingOfIntegers.coe_eq_zero_iff.1 ((map_eq_zero _).1 h1))

omit ν in

theorem exists_local {hle : c.F ≤ c'.F} (hr : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫
      spMap (IntermediateField.inclusion hle).toRingHom) (Z : Comp Xo c) {R : Type} [CommRing R]
    {ξ : Sp R ⟶ Y.X} {b : 𝓞 c'.F →+* R} (hb : ξ ≫ Y.s = spMap b) {k : Type} [Field k] [Algebra c.F k] (ψ : R →+* k)
    {zz : Sp k ⟶ Xo'.XF c'} {z : FrPt Xo c k} (hz : zz ≫ Y.j = spMap ψ ≫ ξ) (hzr : zz ≫ r = GlobalTheory.AllWt.ptF z)
    (hZ : LiesOn Z z) :
    ∃ (𝔮 : Ideal R) (_ : 𝔮.IsPrime) (_ : Algebra c.F (Localization.AtPrime 𝔮))
      (yy : Sp (Localization.AtPrime 𝔮) ⟶ Xo'.XF c') (y : FrPt Xo c (Localization.AtPrime 𝔮))
      (ι : Localization.AtPrime 𝔮 →ₐ[c.F] k), (∀ a, ψ a = ι (algebraMap R _ a)) ∧
      yy ≫ Y.j = spMap (algebraMap R (Localization.AtPrime 𝔮)) ≫ ξ ∧ yy ≫ r = GlobalTheory.AllWt.ptF y ∧ LiesOn Z y := by
  obtain ⟨io, hc', hc⟩ := comp_eq_of_lift Y r hr hb hz hzr
  have hp := RingHom.ker_isPrime ψ
  let L := Localization.AtPrime (RingHom.ker ψ)
  have hu : ∀ a, a ≠ 0 → IsUnit (((algebraMap R L).comp b) a) := fun a ha =>
    IsLocalization.map_units L (⟨b a, fun h => ha (by
      have h1 : ψ (b a) = 0 := h
      have h2 := DFunLike.congr_fun hc' a
      simp only [RingHom.comp_apply] at h2
      rw [h1] at h2
      exact RingOfIntegers.coe_eq_zero_iff.1 ((map_eq_zero _).1 h2.symm))⟩ : (RingHom.ker ψ).primeCompl)
  obtain ⟨alg, halg⟩ := exists_algebra (K := c.F) (((algebraMap R L).comp b).comp (inclO hle)) fun a ha =>
    hu _ (inclO_ne_zero hle ha)
  let ι₀ : L →+* k := IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (g := ψ) fun y => Ne.isUnit y.2
  have hι₀ : ι₀.comp (algebraMap R L) = ψ := IsLocalization.lift_comp _
  obtain ⟨yy, y, hy, hyr, hyZ⟩ := exists_lift_frPt Y r hr Z (spMap (algebraMap R L) ≫ ξ)
    (by rw [Category.assoc, hb, spMap_comp_eq]) hu halg (by
      let s₀ : Sp k := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
      refine ⟨zz s₀, ?_, ?_⟩
      · rw [← Scheme.Hom.comp_apply, hzr]
        exact hZ s₀
      rw [← Scheme.Hom.comp_apply, hz]
      refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg ξ ?_) (Scheme.Hom.comp_apply _ _ _).symm)
      exact PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := RingHom.ker ψ)).symm)
  refine ⟨_, hp, alg, yy, y, algHomOf ι₀ (by
    rw [halg, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hι₀, RingHom.comp_assoc, hc]), fun a => ?_, hy, hyr, hyZ⟩
  exact (DFunLike.congr_fun hι₀ a).symm

include ν in
set_option maxHeartbeats 1000000 in

theorem chart_bound {hle : c.F ≤ c'.F} (hr : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫
      spMap (IntermediateField.inclusion hle).toRingHom) (Z : Comp Xo c) {f : Rul Xo c} {σ₁ σ₂ : E →+* ℂ}
    (hL : DetLaw Z f σ₁ σ₂)
    (hbd : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) → evI y₀ f ∈ (algebraMap T.V T.Fr).range)
    (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (ξ : Sp R ⟶ Y.X) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)) (he : IsTanBasis Y.t ξ e) :
    ∃ m : ℕ, 0 < m ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (φ : R →+* T.V)
      (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp φ) ≫ ξ →
      (letI := io.toAlgebra; yy ≫ r = GlobalTheory.AllWt.ptF y₀.1) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) → (m : T.Fr) * evI y₀ f ∈ (algebraMap T.V T.Fr).range := by
  classical
  by_cases hex : ∃ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (φ : R →+* T.V) (yy : Sp T.Fr ⟶ Xo'.XF c'),
      yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp φ) ≫ ξ ∧ (letI := io.toAlgebra; yy ≫ r = GlobalTheory.AllWt.ptF y₀.1) ∧
      (letI := io.toAlgebra; LiesOn Z y₀.1)
  swap
  · exact ⟨1, one_pos, fun T io y₀ φ yy h1 h2 h3 => (hex ⟨T, io, y₀, φ, yy, h1, h2, h3⟩).elim⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 c'.F →+* R, ξ ≫ Y.s = spMap b := ⟨(Spec.preimage (ξ ≫ Y.s)).hom, by simp [spMap]⟩

  obtain ⟨hbinj, hq⟩ : Function.Injective b ∧
      ∃ q, r q ∈ (Z : Set (Xo.XF c)) ∧ Y.j q = ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
    obtain ⟨T, io, y₀, φ, yy₀, h1, h1', h2⟩ := hex
    letI := io.toAlgebra
    obtain ⟨io', hc, -⟩ := comp_eq_of_lift Y r hr hb h1 h1'
    refine ⟨Function.Injective.of_comp (f := (algebraMap T.V T.Fr).comp φ) ?_, ?_⟩
    · rw [← RingHom.coe_comp, hc]
      exact io'.injective.comp (IsFractionRing.injective (𝓞 c'.F) c'.F)
    · obtain ⟨𝔮, _, _, yy, y, ι, -, hy, hyr, hyZ⟩ := exists_local Y r hr Z hb _ h1 h1' h2
      let s₀ : Sp (Localization.AtPrime 𝔮) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔮))
      refine ⟨yy s₀, ?_, ?_⟩
      · rw [← Scheme.Hom.comp_apply, hyr]
        exact hyZ s₀
      rw [← Scheme.Hom.comp_apply, hy]
      exact bot_map (IsLocalization.injective _ 𝔮.primeCompl_le_nonZeroDivisors) ξ
  haveI : CharZero R := charZero_of_injective_ringHom hbinj
  let F := FractionRing R
  obtain ⟨algF, halgF⟩ := exists_algebra (K := c.F) ((algebraMap R F).comp (b.comp (inclO hle))) fun a ha =>
    Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective R F)).2 ((map_ne_zero_iff _ hbinj).2 (inclO_ne_zero hle ha)))

  have hgen : ∀ (k : Type) [Field k] [Algebra c.F k] (ψ : R →+* k), Function.Injective ψ →
      (algebraMap c.F k).comp (algebraMap (𝓞 c.F) c.F) = ψ.comp (b.comp (inclO hle)) →
      ∃ (yy : Sp k ⟶ Xo'.XF c') (y : FrPt Xo c k), yy ≫ Y.j = spMap ψ ≫ ξ ∧ yy ≫ r = GlobalTheory.AllWt.ptF y ∧ LiesOn Z y :=
    fun k _ _ ψ hψ hk => exists_lift_frPt Y r hr Z (spMap ψ ≫ ξ) (b := ψ.comp b)
      (by rw [Category.assoc, hb, spMap_comp_eq])
      (fun a ha => Ne.isUnit ((map_ne_zero_iff _ hψ).2 ((map_ne_zero_iff _ hbinj).2 ha))) hk (by
      obtain ⟨q, hqZ, hq⟩ := hq
      refine ⟨q, hqZ, hq.trans ((bot_map hψ ξ).symm.trans (congrArg _ ?_))⟩
      exact Subsingleton.elim (α := PrimeSpectrum k) _ _)
  let σR : (E →+* ℂ) → (𝓞 E →+* R) := fun σ => (b.comp (inclO hle)).comp (RingOfIntegers.mapRingHom (embF c σ))
  have hcompat : ∀ (k : Type) [CommRing k] [Algebra c.F k] (ψ : R →+* k) (yy : Sp k ⟶ Xo'.XF c') (y : FrPt Xo c k),
      yy ≫ Y.j = spMap ψ ≫ ξ → yy ≫ r = GlobalTheory.AllWt.ptF y → ∀ σ a, algebraMap c.F k (embK c σ a) = ψ (σR σ a) :=
    fun k _ _ ψ yy y hy hyr σ a =>
      (DFunLike.congr_fun (comp_eq_of_lift Y r hr hb hy hyr).choose_spec.2
        (RingOfIntegers.mapRingHom (embF c σ) a)).symm
  choose U hU using fun σ => exists_isProjMat he (σR σ)
  have hcrd : ∀ (k : Type) [CommRing k] [Algebra c.F k] (ψ : R →+* k) (yy : Sp k ⟶ Xo'.XF c') (y : FrPt Xo c k),
      yy ≫ Y.j = spMap ψ ≫ ξ → yy ≫ r = GlobalTheory.AllWt.ptF y → ∀ σ, ∃ M C, IsCoord Y r ν ξ e (U σ) ψ yy y σ M C :=
    fun k _ _ ψ yy y hy hyr σ => exists_isCoord Y r ν he σ (hU σ) hy hyr (hcompat k ψ yy y hy hyr σ)
  have hint : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (φ : R →+* T.V) (yy : Sp T.Fr ⟶ Xo'.XF c'),
      yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp φ) ≫ ξ → (letI := io.toAlgebra; yy ≫ r = GlobalTheory.AllWt.ptF y₀.1) → ∀ σ,
      ∃ (M₀ : Matrix (Fin (Dw.mult σ)) (Fin g) T.V) (C₀ : Matrix (Fin g) (Fin (Dw.mult σ)) T.V),
        (letI := io.toAlgebra; IsCoord Y r ν ξ e (U σ) ((algebraMap T.V T.Fr).comp φ) yy y₀.1 σ
          (M₀.map (algebraMap T.V T.Fr)) (C₀.map (algebraMap T.V T.Fr))) := fun T io y₀ φ yy h h' σ => by
    letI := io.toAlgebra
    obtain ⟨M, C, hMC⟩ := hcrd T.Fr _ yy y₀.1 h h' σ
    obtain ⟨M₀, C₀, rfl, rfl⟩ := coord_integral Y r ν he σ (hU σ) T io y₀ φ yy h h'
      (hcompat T.Fr _ yy y₀.1 h h' σ) M C hMC
    exact ⟨M₀, C₀, hMC⟩
  obtain ⟨ηη, η, hη, hηr, hηZ⟩ := hgen F (algebraMap R F) (IsFractionRing.injective R F) halgF
  choose Mη Cη hcη using hcrd F _ ηη η hη hηr
  have hden : ∀ p : (Fin (Dw.mult σ₁) → Fin g) × (Fin (Dw.mult σ₂) → Fin g), ∃ (m : ℕ) (s : R), 0 < m ∧
      algebraMap R F s = (m : F) * (evR Xo c f η * ((Mη σ₁).submatrix id p.1).det * ((Cη σ₂).submatrix p.2 id).det) := by
    intro p
    refine exists_nat_mul_mem R _ fun T α ι hα hι hn => ?_
    let io : c.F →+* T.Fr := ι.comp (algebraMap c.F F)
    letI := io.toAlgebra
    have hio : ∀ a, io (algebraMap (𝓞 c.F) c.F a) = algebraMap T.V T.Fr (α (b (inclO hle a))) := fun a =>
      (congrArg ι (DFunLike.congr_fun halgF a)).trans (hι _)
    obtain ⟨zz, z, hz, hzr, hzZ⟩ := hgen T.Fr ((algebraMap T.V T.Fr).comp α)
      ((IsFractionRing.injective T.V T.Fr).comp hα) (RingHom.ext hio)
    obtain ⟨y₀, hy₀⟩ := exists_intFr_lift Y r ν T io (spMap α ≫ ξ) zz z
      (by rw [hz, ← Category.assoc, spMap_comp_eq]) hzr
    have h1 : zz ≫ r = GlobalTheory.AllWt.ptF y₀.1 := hzr.trans hy₀.symm
    have h2 : LiesOn Z y₀.1 := fun s => hy₀ ▸ hzZ s
    obtain ⟨M₁, C₁, h₁⟩ := hint T io y₀ α zz hz h1 σ₁
    obtain ⟨M₂, C₂, h₂⟩ := hint T io y₀ α zz hz h1 σ₂
    have key := value_map Y r ν he hL hη hηr hηZ (hcη σ₁) (hcη σ₂)
      ({ ι with commutes' := fun _ => rfl } : F →ₐ[c.F] T.Fr) (fun a => (hι a).symm) hz h1 h₁ h₂ p.1 p.2
    obtain ⟨s, hs⟩ := hbd T io y₀ (vV_eq_zero T io (α.comp (b.comp (inclO hle))) hio hn) h2
    refine ⟨s * (M₁.submatrix id p.1).det * (C₂.submatrix p.2 id).det, Eq.trans ?_ key⟩
    rw [map_mul, map_mul, hs, RingHom.map_det, RingHom.map_det]
    rfl
  choose m s hm hs using hden
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  refine ⟨(∏ p, m p) * (discr E).natAbs ^ (Dw.mult σ₁ + Dw.mult σ₂),
    Nat.mul_pos (Finset.prod_pos fun p _ => hm p) (Nat.pos_of_ne_zero (pow_ne_zero _ hd0)), fun T io y₀ φ yy₀ h1 h1' h2 => ?_⟩
  letI := io.toAlgebra
  have hinj := IsFractionRing.injective T.V T.Fr
  obtain ⟨M₁, C₁, h₁⟩ := hint T io y₀ φ yy₀ h1 h1' σ₁
  obtain ⟨M₂, C₂, h₂⟩ := hint T io y₀ φ yy₀ h1 h1' σ₂
  have hδ : ((discr E : ℤ) : T.V) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have hMC : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin g) T.V) (C : Matrix (Fin g) (Fin n) T.V),
      M.map (algebraMap T.V T.Fr) * C.map (algebraMap T.V T.Fr) = ((discr E : ℤ) : T.Fr) • 1 →
      M * C = ((discr E : ℤ) : T.V) • 1 := fun M C h => by
    ext i j
    apply hinj
    have := congrFun (congrFun h i) j
    rw [← Matrix.map_mul] at this
    refine this.trans ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  obtain ⟨⟨I, d₁, hd₁⟩, -⟩ := exists_minor_dvd T.V _ _ M₁ C₁ _ hδ (hMC _ _ h₁.2.2)
  obtain ⟨-, J, d₂, hd₂⟩ := exists_minor_dvd T.V _ _ M₂ C₂ _ hδ (hMC _ _ h₂.2.2)
  obtain ⟨𝔮, _, _, yy, y, ι₂, hι₂, hy, hyr, hyZ⟩ := exists_local Y r hr Z hb _ h1 h1' h2
  let L := Localization.AtPrime 𝔮
  choose ML CL hcL using hcrd L _ yy y hy hyr
  let j₀ : L →+* F := IsLocalization.lift (M := 𝔮.primeCompl) (g := algebraMap R F) fun a =>
    IsLocalization.map_units F (⟨a, 𝔮.primeCompl_le_nonZeroDivisors a.2⟩ : nonZeroDivisors R)
  have hj₀ : j₀.comp (algebraMap R L) = algebraMap R F := IsLocalization.lift_comp _
  have hj₀inj : Function.Injective j₀ := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (M := 𝔮.primeCompl)]
    intro a a'
    have e1 : ∀ a, j₀ (algebraMap R L a) = algebraMap R F a := fun a => DFunLike.congr_fun hj₀ a
    rw [e1, e1, (IsFractionRing.injective R F).eq_iff,
      (IsLocalization.injective L 𝔮.primeCompl_le_nonZeroDivisors).eq_iff]
  let ι₁ : L →ₐ[c.F] F := algHomOf j₀ (by
    rw [← (comp_eq_of_lift Y r hr hb hy hyr).choose_spec.2, ← RingHom.comp_assoc, hj₀, halgF])
  have k1 := value_map Y r ν he hL hy hyr hyZ (hcL σ₁) (hcL σ₂) ι₁ (fun a => (DFunLike.congr_fun hj₀ a).symm) hη hηr
    (hcη σ₁) (hcη σ₂) I J
  have k2 := value_map Y r ν he hL hy hyr hyZ (hcL σ₁) (hcL σ₂) ι₂ hι₂ h1 h1' h₁ h₂ I J
  generalize evR Xo c f y * ((ML σ₁).submatrix id I).det * ((CL σ₂).submatrix J id).det = u at k1 k2
  have k3 : algebraMap R L (s (I, J)) = (m (I, J) : L) * u := hj₀inj (by
    rw [map_mul, map_natCast]
    exact (DFunLike.congr_fun hj₀ _).trans ((hs (I, J)).trans (congrArg _ k1)))
  have k4 : algebraMap T.V T.Fr (φ (s (I, J))) = (m (I, J) : T.Fr) * (evI y₀ f *
      algebraMap T.V T.Fr (M₁.submatrix id I).det * algebraMap T.V T.Fr (C₂.submatrix J id).det) := by
    refine (hι₂ _).trans ?_
    rw [k3, map_mul, map_natCast, ← k2, RingHom.map_det, RingHom.map_det]
    rfl
  obtain ⟨m', hm'⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (I, J))
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (((discr E).natAbs : ℕ) : ℤ) = ε * discr E := by
    rcases Int.natAbs_eq (discr E) with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨-1, by omega⟩
  refine ⟨(m' : T.V) * (ε : T.V) ^ (Dw.mult σ₁ + Dw.mult σ₂) * d₁ * d₂ * φ (s (I, J)), ?_⟩
  have e1 := congrArg (algebraMap T.V T.Fr) hd₁
  have e2 := congrArg (algebraMap T.V T.Fr) hd₂
  have e3 : (((discr E).natAbs : ℕ) : T.Fr) = (ε : T.Fr) * ((discr E : ℤ) : T.Fr) := by
    rw [← Int.cast_mul, ← hε, Int.cast_natCast]
  simp only [map_mul, map_pow, map_intCast] at e1 e2
  simp only [map_mul, map_pow, map_intCast, map_natCast, k4, hm', Nat.cast_mul, Nat.cast_pow, e3, mul_pow, pow_add, e1, e2]
  ring

omit Y r ν in
set_option maxHeartbeats 1000000 in

theorem exists_denom (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (Z : Comp Xo c)
    {f : Rul Xo c} {σ₁ σ₂ : E →+* ℂ} (hL : DetLaw Z f σ₁ σ₂)
    (hbd : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) → evI y₀ f ∈ (algebraMap T.V T.Fr).range) :
    ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • f) := by
  classical
  obtain ⟨l', hd, hA', hg⟩ := GlobalTheory.GoodMultipleLevel.exists_good_multiple E H l
  haveI := c.fin
  obtain ⟨c', hle⟩ := GlobalTheory.TupleCover.exists_coeff_ge l' c.F
  let X : ∀ l : Level H, Moduli Dw l := fun l₁ => Classical.choice (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₁ hpq)
  obtain ⟨Y₀, -, h6⟩ := GlobalTheory.partI_closed.2 E H Dw hpq X
  obtain ⟨Y, -⟩ := h6 l' c' hg (hA'.trans hA)
  obtain ⟨r, hr, r₀, m₀, hr₀, hfin, -, hsurj⟩ :=
    GlobalTheory.LevelMapBase.levelMap_coeff_le E H Dw l l' Xo (X l') c c' hle hpq hd
  obtain ⟨ν₀, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ Y.m0.toSABMap
  obtain ⟨ν, -⟩ := GlobalTheory.ModelFrameCompare.exists_sabMap_congr ν₀ hr₀.symm
  have hN : GlobalTheory.IsNormalScheme Y.X := (GlobalTheory.isNormalScheme_iff _).2 Y.normal
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have loc : ∀ x : Y.X, ∃ (V : Y.X.Opens) (m : ℕ), x ∈ V ∧ 0 < m ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yt : Sp T.V ⟶ Y.X) (yy : Sp T.Fr ⟶ (X l').XF c'),
        yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → (letI := io.toAlgebra; yy ≫ r = GlobalTheory.AllWt.ptF y₀.1) →
        yt (IsLocalRing.closedPoint T.V) ∈ V → (letI := io.toAlgebra; LiesOn Z y₀.1) →
        (m : T.Fr) * evI y₀ f ∈ (algebraMap T.V T.Fr).range := fun x => by
    obtain ⟨V, g, e, hxV, he⟩ := exists_affine_isTanBasis E H Y.X Y.t Y.X (𝟙 _) x
    obtain ⟨U, hU, hd, hxU, hle, hic⟩ := exists_affine_normal_domain V.1 hxV
    obtain ⟨ρ, eρ⟩ : ∃ ρ : Γ(Y.X, V.1) →+* Γ(Y.X, U), spMap ρ ≫ V.2.fromSpec = hU.fromSpec :=
      ⟨(Y.X.presheaf.map (homOfLE hle).op).hom, V.2.map_fromSpec hU _⟩
    have hb := isTanBasis_bc he ρ
    rw [Category.comp_id, eρ] at hb
    have : IsNoetherianRing Γ(Y.X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨m, hm, h⟩ := chart_bound Y r ν hr Z hL hbd Γ(Y.X, U) hU.fromSpec _ hb
    refine ⟨U, m, hxU, hm, fun T io y₀ yt yy h1 h1' h2 h3 => ?_⟩
    obtain ⟨φ, rfl⟩ := GlobalTheory.localSpec_fac_of_closedPoint_mem_range T.V Y.X Γ(Y.X, U) hU.fromSpec yt inferInstance
      (by rw [hU.range_fromSpec]; exact h2)
    exact h T io y₀ φ yy (by rw [h1, ← Category.assoc, spMap_comp_eq]) h1' h3
  choose V m hV hm hloc using loc
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set Y.X)) (fun x => (V x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hV x⟩
  refine ⟨∏ x ∈ S, m x, Finset.prod_pos fun x _ => hm x, fun la v hv => ?_⟩
  obtain ⟨⟨_, T, io, e₀, ho, y₀, hy, η, -, rfl⟩, rfl⟩ := hv

  letI : Algebra c.F c'.F := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by simp
  haveI := c'.fin
  haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ c.F c'.F
  obtain ⟨L₀, _, _, _, io', hio'⟩ := GlobalTheory.LevelLift.exists_field_over c.F c'.F T.Fr io
  letI := io.toAlgebra
  have cond : (spMap (algebraMap T.Fr L₀) ≫ GlobalTheory.AllWt.ptF y₀.1) ≫ pullback.snd _ _ =
      spMap io' ≫ spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, GlobalTheory.AllWt.ptF, pullback.lift_snd, spMap_comp_eq, spMap_comp_eq]
    exact congrArg spMap hio'.symm
  obtain ⟨L, _, _, _, x', hx'⟩ := GlobalTheory.LevelLift.exists_point_finite_surjective _ hfin hsurj L₀ (pullback.lift _ _ cond)
  letI : Algebra T.Fr L := ((algebraMap L₀ L).comp (algebraMap T.Fr L₀)).toAlgebra
  haveI : IsScalarTower T.Fr L₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional T.Fr L := Module.Finite.trans L₀ L
  obtain ⟨T', iT, e', ψ, φ, he', hv, hψ, hφ, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
  obtain ⟨y₁, ι, hι, hm₁⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y₀ iT e' he'
    fun a _ => hv a
  letI := (iT.comp io).toAlgebra
  have hx1 : x' ≫ r = spMap (algebraMap T.Fr L) ≫ GlobalTheory.AllWt.ptF y₀.1 := by
    have h := congrArg (· ≫ pullback.fst _ _) hx'
    simp only [Category.assoc, pullback.lift_fst] at h
    rw [h, ← Category.assoc, spMap_comp_eq]
  have hc : ψ.toRingHom.comp (algebraMap T.Fr L) = iT := RingHom.ext fun a => hψ a
  have hpt : GlobalTheory.AllWt.ptF y₁.1 = spMap iT ≫ GlobalTheory.AllWt.ptF y₀.1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_fst, pullback.lift_fst, hm₁.1, hι]
    · rw [Category.assoc, GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd, spMap_comp_eq]
  have hyr : (spMap ψ.toRingHom ≫ x') ≫ r = GlobalTheory.AllWt.ptF y₁.1 := by
    rw [Category.assoc, hx1, ← Category.assoc, spMap_comp_eq, hc, hpt]
  obtain ⟨io₂, hio₂⟩ : ∃ io₂ : c'.F →+* T'.Fr, spMap io₂ = (spMap ψ.toRingHom ≫ x') ≫ pullback.snd _ _ :=
    ⟨(Spec.preimage ((spMap ψ.toRingHom ≫ x') ≫ pullback.snd _ _)).hom, by simp [spMap]⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 c'.F →+* T'.V, (algebraMap T'.V T'.Fr).comp b = io₂.comp (algebraMap (𝓞 c'.F) c'.F) := by
    have key : ∀ a : 𝓞 c'.F, io₂ (algebraMap (𝓞 c'.F) c'.F a) ∈ (algebraMap T'.V T'.Fr).range := fun a => by
      obtain ⟨p, hp, h0⟩ := RingOfIntegers.isIntegral a
      refine IsIntegrallyClosed.isIntegral_iff (R := T'.V) (K := T'.Fr).1
        ⟨p.map (Int.castRingHom T'.V), hp.map _, ?_⟩
      have h1 := congrArg (io₂.comp (algebraMap (𝓞 c'.F) c'.F)) h0
      rw [Polynomial.hom_eval₂, map_zero] at h1
      rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T'.V T'.Fr).comp (Int.castRingHom T'.V))
        ((io₂.comp (algebraMap (𝓞 c'.F) c'.F)).comp (algebraMap ℤ (𝓞 c'.F)))]
      exact h1
    let eq := RingEquiv.ofBijective (algebraMap T'.V T'.Fr).rangeRestrict
      ⟨fun a a' h => IsFractionRing.injective T'.V T'.Fr (congrArg Subtype.val h),
        (algebraMap T'.V T'.Fr).rangeRestrict_surjective⟩
    refine ⟨eq.symm.toRingHom.comp ((io₂.comp (algebraMap (𝓞 c'.F) c'.F)).codRestrict _ key), RingHom.ext fun a => ?_⟩
    exact congrArg Subtype.val (eq.apply_symm_apply _)
  obtain ⟨yt, h1, -⟩ := extPt Y T' b (spMap ψ.toRingHom ≫ x') (by
    show _ = spMap (algebraMap T'.V T'.Fr) ≫ spMap b
    rw [openImmersion_comp_structure_eq_generic, ← Category.assoc, ← hio₂, spMap_comp_eq, spMap_comp_eq, hb])
  obtain ⟨x, hx, hxV⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ (yt (IsLocalRing.closedPoint T'.V))))
  obtain ⟨s, hs⟩ := hloc x T' _ y₁ yt _ h1.symm hyr hxV (fun p => by
    rw [hpt, Scheme.Hom.comp_apply]
    exact hy.2 _)
  have hev : evI y₁ f = iT (evI y₀ f) := (GlobalTheory.FlagTan.evR_frMap hL.1 hm₁).trans (DFunLike.congr_fun hι _)
  obtain ⟨m', hm'⟩ := Finset.dvd_prod_of_mem m hx
  show 0 ≤ nval T.V e₀ (evI y₀ _)
  rw [← nval_bc iT he' hv, evI_smul, map_natCast, map_mul, map_natCast, ← hev, hm', Nat.cast_mul,
    mul_comm (m x : T'.Fr), mul_assoc, ← hs, ← map_natCast (algebraMap T'.V T'.Fr), ← map_mul]
  generalize (m' : T'.V) * s = t
  by_cases h0 : algebraMap T'.V T'.Fr t = 0
  · rw [h0, nval_zero]; exact le_top
  have := (WithZero.log_le_log (valV_ne_zero (V := T'.V) h0) one_ne_zero).2
    (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ t)
  rw [WithZero.log_one] at this
  rw [nval_of_ne h0, EReal.coe_nonneg]
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  have h2 : 0 ≤ vV T'.V (algebraMap T'.V T'.Fr t) := by rw [vV]; omega
  exact_mod_cast h2

end GlobalTheory.FlatDenom.Cover

end
