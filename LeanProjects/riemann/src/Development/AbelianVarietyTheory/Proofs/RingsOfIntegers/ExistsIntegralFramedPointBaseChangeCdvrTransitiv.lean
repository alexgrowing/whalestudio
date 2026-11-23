import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PlaceInt.Ext

section Sections

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.AbLaw.PerfOfModel

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {Y Y' : Scheme.{0}}
  {f : Y ⟶ Spec (CommRingCat.of R)} {f' : Y' ⟶ Spec (CommRingCat.of R')} {π : Y' ⟶ Y} {M : LB Y}

theorem baseChangeHom_top_bijective [Module.Flat R R'] [CompactSpace Y] [IsSeparated f] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Function.Bijective (SecOnR.baseChangeHom M H.w ⊤ ⊤ le_top) := by
  obtain ⟨s, hs', hs⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    (⟨isCompact_univ, isOpen_univ⟩ : IsCompact (Set.univ : Set Y) ∧ IsOpen (Set.univ : Set Y))
  have := hs'.fintype
  let e := (Fintype.equivFin s).symm
  let D : Fin (Fintype.card s) → Y.Opens := fun i => (e i).1.1
  have hc : ⨆ i, D i = ⊤ := by
    rw [e.iSup_comp (g := fun i : s => i.1.1)]
    ext1
    simpa using hs.symm
  have : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from f]
    infer_instance
  have hD : ∀ I : Finset (Fin (Fintype.card s)), I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i) := fun I hI =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hI) fun i _ => (e i).1.2
  have hc' := iSup_preimage π hc
  let c := CechOne.toCech M f D (V := ⊤) fun _ => le_top
  let c' := CechOne.toCech (M.pull π) f' (fun i => π ⁻¹ᵁ D i) (V := ⊤) fun _ => le_top
  have ci : Function.Injective c := CechOne.toCech_injective M f _ hc.ge
  have ci' : Function.Injective c' := CechOne.toCech_injective _ f' _ hc'.ge
  have ex := Module.Flat.lTensor_exact R' (CechOne.exact_toCech M f (V := ⊤) (fun _ => le_top) hc.ge)
  have ex' := CechOne.exact_toCech (M.pull π) f' (V := ⊤) (fun _ => le_top) hc'.ge
  have sq : ∀ x, c' (SecOnR.baseChangeHom M H.w ⊤ ⊤ le_top x) = termMap M D H.w 0 (c.lTensor R' x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      funext I
      exact (SecOnR.baseChangeHom_restrict H.w le_top le_top le_top (preimage_biInf D π I.1).ge (a ⊗ₜ x)).symm
  have B := termMap_bijOn hM H hD
  refine ⟨fun x y h => Module.Flat.lTensor_preserves_injective_linearMap (M := R') c ci
    ((termMap_bijective hM H hD 0).1 ((sq x).symm.trans ((congrArg c' h).trans (sq y)))), fun y => ?_⟩
  obtain ⟨x, hx, hxy⟩ := B.2.2 (show c' y ∈ LinearMap.ker _ from (ex' _).2 ⟨y, rfl⟩)
  obtain ⟨z, rfl⟩ := (ex x).1 hx
  exact ⟨z, ci' ((sq z).trans hxy)⟩

theorem eq_smul_iff (x y : SecOnR f M ⊤) (a : R) : x = a • y ↔
    ∀ i, (SecOnR.topEquiv f M x).f i = cst f _ a * (SecOnR.topEquiv f M y).f i := by
  have e : ∀ i, (SecOnR.topEquiv f M (a • y)).f i = cst f _ a * (SecOnR.topEquiv f M y).f i := fun i => by
    rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_base_smul, map_mul, rs_cst]
  refine ⟨fun h i => h ▸ e i, fun h => (SecOnR.topEquiv f M).injective
    (DVR.SecOps.sec_ext fun i => (h i).trans (e i).symm)⟩

theorem existsUnique_mul_pull [Module.Flat R R'] [CompactSpace Y] [IsSeparated f] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (θ : LB.Sec M)
    (hθ : ∀ σ : LB.Sec M, ∃! a : R, ∀ i, σ.f i = cst f _ a * θ.f i) (σ : LB.Sec (M.pull π)) :
    ∃! a : R', ∀ i, σ.f i = cst f' _ a * (Formalism.L2.Pj.thfPull M π θ).f i := by
  obtain ⟨t, rfl⟩ := (SecOnR.topEquiv f M).surjective θ
  obtain ⟨s, rfl⟩ := (SecOnR.topEquiv f' (M.pull π)).surjective σ
  have e₁ : Formalism.L2.Pj.thfPull M π (SecOnR.topEquiv f M t) =
      SecOnR.topEquiv f' (M.pull π) (SecOnR.pull M H.w ⊤ ⊤ le_top t) := by
    refine (DVR.SecOps.sec_ext fun i => ?_).symm
    refine (congrArg (rs Y' _) (SecOn.coord_pullLE π le_top t i)).trans ?_
    change (π.appLE _ _ _ ≫ Y'.presheaf.map _).hom _ = (Y.presheaf.map _ ≫ π.appLE _ _ _).hom _
    rw [Scheme.Hom.appLE_map]
    exact (GlobalTheory.LB.appLE_resG π (le_inf le_top le_rfl) _ _).symm
  have b : Function.Bijective (LinearMap.toSpanSingleton R _ t) :=
    (Function.bijective_iff_existsUnique _).2 fun x =>
      (existsUnique_congr fun a => (eq_smul_iff x t a).symm.trans eq_comm).1 (hθ _)
  have b' := ((baseChangeHom_top_bijective hM H).comp
    ((LinearEquiv.ofBijective _ b).lTensor R').bijective).comp (TensorProduct.rid R R').symm.bijective
  rw [e₁]
  refine (existsUnique_congr fun a => ?_).1 ((Function.bijective_iff_existsUnique _).1 b' s)
  rw [← eq_smul_iff, eq_comm]
  simp
  rfl

open Geo.Tor Formalism.L2.Pj in

theorem existsUnique_mul_of_isoMaps {L' : LB Y'} (hM : M.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (M.pull π)}
    (hw : w.IsGen) (θ' : LB.Sec L') (θ : LB.Sec (M.pull π)) (h : IsoMaps w θ' θ)
    (hθ : ∀ σ : LB.Sec (M.pull π), ∃! a : R', ∀ i, σ.f i = constFn f' _ a * θ.f i) (σ' : LB.Sec L') :
    ∃! a : R', ∀ i, σ'.f i = constFn f' _ a * θ'.f i := by
  obtain ⟨σ, hσ⟩ := thf_secUp ((isGen_iff w).1 hw) hM hL' σ'
  have ht : ∀ (y : Y') (J : PUnit → M.ι) k, y ∈ (M.pull π).U J → y ∈ L'.U k →
      gs (𝟙 _) y _ (θ.f J) = (gw w (𝟙 _) y (J PUnit.unit) k).val * gs (𝟙 _) y _ (θ'.f k) := by
    intro y J k hj hk
    have hz : (𝟙 Y' : Y' ⟶ Y') y ∈ (M.pull π).U J ⊓ L'.U k := ⟨hj, hk⟩
    exact (gs_res _ y _ hz _).symm.trans ((congrArg (gs (𝟙 _) y _) (h J k)).trans ((gs_mul _ y _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
  refine (existsUnique_congr fun a => ⟨fun ha k => fn_ext fun y hy => ?_,
    fun ha (J : PUnit → M.ι) => fn_ext fun y hy => ?_⟩).1 (hθ σ)
  · obtain ⟨j, hj⟩ := exists_chart hM (π y)
    have hj' : (𝟙 Y' : Y' ⟶ Y') y ∈ (M.pull π).U fun _ => j := mem_pull.2 hj
    have e := (hσ _ (𝟙 _) y (fun _ => j) k hj' hy).symm.trans ((congrArg (gs (𝟙 _) y _) (ha _)).trans
      ((gs_mul _ y _ hj' _ _).trans (congrArg₂ (· * ·) (gs_constFn _ _ _ y hj' a) (ht y _ k hj' hy))))
    rw [mul_left_comm, Units.mul_right_inj] at e
    rw [gs_mul _ y _ hy, gs_constFn _ _ _ y hy, e]
  · obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (hσ _ (𝟙 _) y J k hy hk).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_constFn _ _ _ y hy a) (ht y _ k hy hk))).symm)
    rw [ha, gs_mul _ y _ hk, gs_constFn _ _ _ y hk, mul_left_comm]

end Sections

section Lie

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.LieRel
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec univChartLoc tanBC_alg
  pushR pushR_left pushR_map tvec_tmap fB dualMapA pushR_inj)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_eigenbasis_pullback {V V' : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing V']
    [Algebra V V'] [Module.Flat V V'] (G : Over (Sp V)) [GrpObj G] [Smooth G.hom] {O : Type} (act : O → (G ⟶ G))
    [∀ a, IsMonHom (act a)] (χ : O → V) {m : ℕ} (u : Fin m → (epsOver V V ⟶ G)) (ht : ∀ i, IsTan (u i))
    (he : ∀ i a, (u i ≫ act a).left = spMap (epsMul (χ a)) ≫ (u i).left)
    (hb : ∀ w : epsOver V V ⟶ G, IsTan w → (∀ a, (w ≫ act a).left = spMap (epsMul (χ a)) ≫ w.left) →
      ∃! c : Fin m → V, IsComb u c w) :
    ∃ u' : Fin m → (epsOver V' V' ⟶ (Over.pullback (fB V V')).obj G), (∀ i, IsTan (u' i)) ∧
      (∀ i a, (u' i ≫ (Over.pullback (fB V V')).map (act a)).left =
        spMap (epsMul (algebraMap V V' (χ a))) ≫ (u' i).left) ∧
      (∀ w : epsOver V' V' ⟶ (Over.pullback (fB V V')).obj G, IsTan w →
        (∀ a, (w ≫ (Over.pullback (fB V V')).map (act a)).left = spMap (epsMul (algebraMap V V' (χ a))) ≫ w.left) →
        ∃! c : Fin m → V', IsComb u' c w) ∧
      ∀ i, (u' i).left ≫ pullback.fst G.hom (fB V V') = spMap (dualMap (algebraMap V V')) ≫ (u i).left := by
  obtain ⟨n, xc, hxc⟩ := univChartLoc G
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := V) (R' := V') G n xc hxc
  have hpt : ∀ cc : Fin n → V, pushR G (tvec (x := x') (algebraMap V V' ∘ cc)) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (dualMapA V V') ≫ tvec (x := xc) cc := fun cc =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp cc]; rfl)
  have hM : ∀ (a : O) (cc : Fin n → V),
      tmap hx' ((Over.pullback (fB V V')).map (act a)) (algebraMap V V' ∘ cc) =
        algebraMap V V' ∘ tmap hxc (act a) cc := by
    intro a cc
    apply tvec_inj hx'
    apply pushR_inj G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hxc, Category.assoc]
  let M : O → Matrix (Fin n) (Fin n) V := fun a => (LinearMap.toMatrix' (tmap hxc (act a)))ᵀ
  have hM₀ : ∀ a v, v ᵥ* M a = tmap hxc (act a) v := fun a v => by
    rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  have hM₁ : ∀ a v, v ᵥ* (M a).map (algebraMap V V') = tmap hx' ((Over.pullback (fB V V')).map (act a)) v := by
    intro a v
    have : ((M a).map (algebraMap V V')).vecMulLinear = tmap hx' ((Over.pullback (fB V V')).map (act a)) := by
      refine (Pi.basisFun V' (Fin n)).ext fun j => ?_
      have e : Pi.basisFun V' (Fin n) j = algebraMap V V' ∘ Pi.single j 1 := by
        funext k
        by_cases h : k = j <;> simp [h]
      rw [e, hM, ← hM₀]
      funext k
      exact (RingHom.map_vecMul (algebraMap V V') (M a) (Pi.single j 1) k).symm
    exact LinearMap.congr_fun this v
  choose b hb' using fun i => tan_eq_cvV hxc (ht i)
  obtain rfl : u = fun i => cvV (tvec (x := xc) (b i)) := funext hb'
  have hbe : ∀ i a, tmap hxc (act a) (b i) = χ a • b i := fun i a => (eigV_iff hxc (act a) (b i) _).1 (he i a)
  have key := (GlobalTheory.commonEigenvectors_flat_baseChange V O n m M χ).1 V b (fun k a => by rw [hM₀, hbe])
    (fun w hw => by
      have hw' : ∀ a, tmap hxc (act a) w = χ a • w := fun a => by
        rw [← hM₀]
        simpa using hw a
      exact (existsUnique_congr fun c => comb_iff hxc b c w).1
        (hb _ (isTan_cvV (isTan_tvec hxc w)) fun a => (eigV_iff hxc (act a) w _).2 (hw' a))) V'
  refine ⟨fun i => cvV (tvec (x := x') (algebraMap V V' ∘ b i)), fun i => isTan_cvV (isTan_tvec hx' _),
    fun i a => (eigV_iff hx' _ _ _).2 ?_, fun w hw hwe => ?_, fun i => ?_⟩
  · rw [hM, hbe]
    funext k
    simp
  · obtain ⟨v, rfl⟩ := tan_eq_cvV hx' hw
    exact (existsUnique_congr fun c => comb_iff hx' (fun i => algebraMap V V' ∘ b i) c v).2
      (key v fun a => (hM₁ a v).trans ((eigV_iff hx' _ _ _).1 (hwe a)))
  · rw [cvV_left, cvV_left]
    exact hcomp (b i)

end Lie

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_restrict (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ)
    (h : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) :
    ∃ φ : T.V →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a) := by
  have key : ∀ a : T.V, iT (algebraMap T.V T.Fr a) ∈ (algebraMap T'.V T'.Fr).range := by
    intro a
    by_cases h0 : algebraMap T.V T.Fr a = 0
    · rw [h0, map_zero]; exact zero_mem _
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
    have h3 : 0 ≤ vV T'.V (iT (algebraMap T.V T.Fr a)) := by
      rw [h]
      refine mul_nonneg (Nat.cast_nonneg e) ?_
      rw [WithZero.log_one] at h2
      unfold vV
      omega
    have h4 : valV T'.V (iT (algebraMap T.V T.Fr a)) ≤ 1 := by
      refine (WithZero.log_le_log (valV_ne_zero ((map_ne_zero iT).2 h0)) one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h3
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T'.V) (K := T'.Fr) h4
  let j := RingEquiv.ofBijective (algebraMap T'.V T'.Fr).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective T'.V T'.Fr (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  exact ⟨j.symm.toRingHom.comp ((iT.comp (algebraMap T.V T.Fr)).codRestrict _ key),
    fun a => congrArg Subtype.val (j.apply_symm_apply ⟨_, key a⟩)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

open GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique in

theorem integral_of_frMap (T T' : CDVR) (io : c.F →+* T.Fr) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V)
    (hφ : ∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) :
    letI := io.toAlgebra
    letI := (iT.comp io).toAlgebra
    ∀ (ψ : T.Fr →ₐ[c.F] T'.Fr) (y : FrPt Xo c T.Fr) (y' : FrPt Xo c T'.Fr), ψ.toRingHom = iT → FrMap ψ y y' →
      Integral T io y → Integral T' (iT.comp io) y' := by
  let _ := io.toAlgebra
  let _ := (iT.comp io).toAlgebra
  intro ψ y y' hψ hm ⟨G, t, m1, m2, ⟨ub, u₁, u₂, u₃, u₄⟩, θ, hθ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩
  let _ := φ.toAlgebra
  have inj : Function.Injective (algebraMap T.V T'.V) := fun a b h => IsFractionRing.injective T.V T.Fr
    (iT.injective ((hφ a).symm.trans ((congrArg _ h).trans (hφ b))))
  have : FaithfulSMul T.V T'.V := (faithfulSMul_iff_algebraMap_injective _ _).2 inj
  have : Module.Flat T.V T'.V := inferInstance
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := hm
  let G' := PullbackSections.sabT Out.CubePf.cubePull (spMap φ) G
  let m : SABMap G' G (spMap φ) := PullbackSections.sabM Out.CubePf.cubePull (spMap φ) G
  obtain ⟨t', ⟨n⟩⟩ : ∃ t' : SAB H (Sp T'.Fr), Nonempty (SABMap t' t (spMap ψ.toRingHom)) :=
    ⟨_, ⟨PullbackSections.sabM Out.CubePf.cubePull (spMap ψ.toRingHom) t⟩⟩
  have hι : ψ.toRingHom.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp φ :=
    RingHom.ext fun a => by rw [hψ]; exact (hφ a).symm
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap φ = spMap ψ.toRingHom ≫ spMap (algebraMap T.V T.Fr) := by
    rw [← FrBC.spMap_comp', ← FrBC.spMap_comp', hι]
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨m1', e₁, -⟩ := exists_comp_rig m1 n y'.x hx a1 r0
  obtain ⟨m2', e₂, -⟩ := exists_comp_rig m2 n _ hio a2 r0
  have T₀ := (FrUniq.tie_iff m1 m2 θ y.s).1 ⟨w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩
  have T₁ := FrUniq.tie_pull m1 m2 θ y.s n m1' m2' hx hio e₁ e₂ y'.s pm hs hf (fun Z r z j hz => by
    have hle := FramedBaseChange.chart_le pm hs (fun _ => j)
    rw [← ha _ hle, gs_appLE pm _ _ hle r z hz]) T₀
  obtain ⟨w1', w2', σ', s1', θ2', r1, r2, i1, i2, p2, hg⟩ := (FrUniq.tie_iff m1' m2' θ y'.s).2 T₁
  obtain ⟨m', e₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m m2'
  obtain ⟨w, θ', rw', iw⟩ := pull_sec G G' m θ
  have pw : PullSec m.φ θ (thfPull G.PP.L m.φ θ) := fun _ _ => rfl
  obtain ⟨w', r', i'⟩ := FrBC.exists_isoMaps_cancel m m' m2' rfl e₃ rw' r2 iw pw i2 p2
  have := G.semi.smooth
  have := G.semi.separated
  have := G.semi.quasiCompact
  have := G.act.hom
  have : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
  choose χ hχ using fun τ a => int_val c T io τ a
  have hχ' : ∀ τ a, algebraMap T'.V T'.Fr (algebraMap T.V T'.V (χ τ a)) = (iT.comp io) (embK c τ a) :=
    fun τ a => (hφ _).trans (congrArg iT (hχ τ a))
  choose ub' v₁ v₂ v₃ v₄ using fun τ => exists_eigenbasis_pullback (V' := T'.V) G.G G.act.act (χ τ) (ub τ) (u₁ τ)
    (fun i a => u₂ τ i a _ (hχ τ a)) fun w hw he => u₃ τ w hw fun a z hz => by
      obtain rfl : z = χ τ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ τ a).symm)
      exact he a
  refine ⟨G', t', m1', m', ⟨ub', v₁, fun τ i a z hz => ?_, fun τ w hw he => v₃ τ w hw fun a => he a _ (hχ' τ a),
    fun τ i => ?_⟩, θ', ?_, w1', w', σ', s1', _, r1, r', i1, i', fun _ _ => rfl, hg⟩
  · obtain rfl : z = algebraMap T.V T'.V (χ τ a) :=
      IsFractionRing.injective T'.V T'.Fr (hz.trans (hχ' τ a).symm)
    exact v₂ τ i a
  · obtain ⟨u', b₁, b₂⟩ := u₄ τ i
    have b₃ : u' ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
      have : Mono (spMap (algebraMap T.V T.Fr)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
      refine (cancel_mono (spMap (algebraMap T.V T.Fr))).1 ?_
      have k : (ub τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ i)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, b₂]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k).trans (FrBC.dual_alg _))
    have sq : (spMap (dualMap ψ.toRingHom) ≫ u') ≫ t.G.hom =
        spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap ψ.toRingHom := by
      rw [Category.assoc, b₃, FrBC.dual_alg]
    have l₁ : n.cart.1.lift _ _ sq ≫ n.φ = _ := n.cart.1.lift_fst _ _ _
    have l₂ := n.cart.1.lift_snd _ _ sq
    have fin : ∀ v : Sp (DualNumber T'.V) ⟶ G'.G.left, v ≫ m.φ = spMap (dualMap φ) ≫ (ub τ i).left →
        v ≫ G'.G.hom = spMap (algebraMap T'.V (DualNumber T'.V)) →
        n.cart.1.lift _ _ sq ≫ m'.φ = spMap (dualMap (algebraMap T'.V T'.Fr)) ≫ v := by
      intro v k₁ k₂
      have e₄ : m'.φ ≫ m.φ = n.φ ≫ m2.φ := e₃.symm.trans e₂
      have e₅ : m'.φ ≫ G'.G.hom = _ := m'.cart.1.w
      refine m.cart.1.hom_ext ?_ ?_
      · show (_ ≫ m'.φ) ≫ m.φ = (_ ≫ v) ≫ m.φ
        rw [Category.assoc, Category.assoc, k₁, e₄, ← Category.assoc, l₁, Category.assoc, b₂, ← Category.assoc,
          ← Category.assoc, ← FrBC.dual_comp, ← FrBC.dual_comp, hι]
      · rw [Category.assoc, Category.assoc, k₂, e₅, ← Category.assoc, l₂, FrBC.dual_alg]
    refine ⟨n.cart.1.lift _ _ sq, ?_, fin _ (v₄ τ i) (Over.w (ub' τ i))⟩
    rw [e₁, ← Category.assoc, l₁, Category.assoc, b₁, hu]
  · exact existsUnique_mul_of_isoMaps G.PP.isLB G'.PP.isLB rw'.1 θ' _ iw
      (existsUnique_mul_pull G.PP.isLB m.cart.1 θ hθ)

end Main

end GlobalTheory.PlaceInt.Ext

namespace GlobalTheory.PlaceInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem exists_isExt_and_trans : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e : ℕ), 0 < e → (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) → (∃ y' : IntFr Xo c T' (iT.comp io), IsExt y iT e y') ∧ ∀ y' : IntFr Xo c T' (iT.comp io), IsExt y iT e y' → xOf y' = spMap iT ≫ xOf y ∧ ∀ (T'' : CDVR) (iT' : T'.Fr →+* T''.Fr) (e' : ℕ) (y'' : IntFr Xo c T'' (iT'.comp (iT.comp io))), IsExt y' iT' e' y'' → IsExt y (iT'.comp iT) (e' * e) y'' := by
  intro E _ _ _ H Dw l Xo c T T' io y iT e he hv
  let _ := io.toAlgebra
  let _ := (iT.comp io).toAlgebra
  constructor
  · obtain ⟨φ, hφ⟩ := Ext.exists_restrict T T' iT e hv
    let ψ : T.Fr →ₐ[c.F] T'.Fr := ⟨iT, fun _ => rfl⟩
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c _ _ ψ y.1
    obtain ⟨p, ρ, y₀, h₀⟩ := y.2.1
    exact ⟨⟨z, ⟨p, ψ.comp ρ, y₀, GlobalTheory.FramedBaseChange.trans ρ ψ h₀ hz⟩,
      Ext.integral_of_frMap T T' io iT φ hφ ψ y.1 z rfl hz y.2.2⟩, he, hv, ψ, rfl, hz⟩
  · rintro y' ⟨-, -, ψ, hψ, hm⟩
    refine ⟨hm.1.trans (by rw [hψ]), ?_⟩
    rintro T'' iT' e' y'' ⟨he', hv', ψ', hψ', hm'⟩
    let _ := (iT'.comp (iT.comp io)).toAlgebra
    refine ⟨Nat.mul_pos he' he, fun a => ?_, ψ'.comp ψ, ?_, GlobalTheory.FramedBaseChange.trans ψ ψ' hm hm'⟩
    · rw [RingHom.comp_apply, hv', hv, Nat.cast_mul, _root_.mul_assoc]
    · exact congrArg₂ RingHom.comp hψ' hψ

end GlobalTheory.PlaceInt
