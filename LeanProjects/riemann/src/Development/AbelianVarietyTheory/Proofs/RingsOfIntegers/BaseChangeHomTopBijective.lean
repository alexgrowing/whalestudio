import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLetterRingBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaBound.Ext

section Sections

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.AbLaw.PerfOfModel

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {Y Y' : Scheme.{0}}
  {f : Y ⟶ Spec (CommRingCat.of R)} {f' : Y' ⟶ Spec (CommRingCat.of R')} {π : Y' ⟶ Y} {M : LB Y}

theorem baseChangeHom_top_bijective [Module.Flat R R'] [CompactSpace Y] [IsSeparated f] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Function.Bijective (SecOnR.baseChangeHom M H.w ⊤ ⊤ le_top) := by
  classical
  have e0 : (⊤ : Y'.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  show Function.Bijective (SecOnR.baseChangeHom M H.w ⊤ ⊤ e0)
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from f]
    infer_instance
  obtain ⟨s, hs, hcov⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := Y) (U := ⊤)).mp
    (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  let t := hs.toFinset
  let D : Fin t.card → Y.Opens := fun k => ((t.equivFin.symm k : t) : Y.affineOpens)
  have hDa : ∀ k, IsAffineOpen (D k) := fun k => ((t.equivFin.symm k : t) : Y.affineOpens).2
  have hD : ∀ I : Finset (Fin t.card), I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i) := fun I hI =>
    IsAffineOpen.biInf (I : Set (Fin t.card)) I.finite_toSet hI (fun k _ => hDa k)
  have hc : ⨆ k, D k = ⊤ := by
    refine top_unique ?_
    rw [hcov]
    refine iSup₂_le fun i hi => ?_
    have hit : i ∈ t := hs.mem_toFinset.mpr hi
    refine le_trans (le_of_eq ?_) (le_iSup D (t.equivFin ⟨i, hit⟩))
    simp [D]
  have hc' : ⨆ k, π ⁻¹ᵁ D k = ⊤ := iSup_preimage π hc
  let toC := CechOne.toCech M f D (fun _ => le_top)
  let toC' := CechOne.toCech (M.pull π) f' (fun k => π ⁻¹ᵁ D k) (fun _ => le_top)
  have hinj' : Function.Injective toC' :=
    CechOne.toCech_injective (M.pull π) f' (D := fun k => π ⁻¹ᵁ D k) (fun _ => le_top) hc'.ge
  have hex' : Function.Exact toC' ((cechLB f' (M.pull π) fun k => π ⁻¹ᵁ D k).d 0 1).hom :=
    CechOne.exact_toCech (M.pull π) f' (D := fun k => π ⁻¹ᵁ D k) (fun _ => le_top) hc'.ge
  have hflat : Function.Injective (toC.baseChange R') := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (CechOne.toCech_injective M f (D := D) (fun _ => le_top) hc.ge)
  have hexR : Function.Exact (toC.baseChange R') (((cechLB f M D).d 0 1).hom.baseChange R') := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact R' (CechOne.exact_toCech M f (D := D) (fun _ => le_top) hc.ge)
  have compat : ∀ x, toC' (SecOnR.baseChangeHom M H.w ⊤ ⊤ e0 x) =
      termMap M D H.w 0 (toC.baseChange R' x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c s0 =>
      funext u
      rw [LinearMap.baseChange_tmul, SecOnR.baseChangeHom_tmul]
      unfold termMap
      erw [secTermBaseChange_tmul, LinearMap.map_smul, Pi.smul_apply]
      erw [CechOne.toCech_apply (M.pull π) f' (fun k => π ⁻¹ᵁ D k) (fun _ => le_top) _ u le_top]
      erw [CechOne.toCech_apply M f D (fun _ => le_top) s0 u le_top]
      congr 1
      have h1 := SecOnR.baseChangeHom_restrict H.w (le_top : (⨅ i ∈ u.1, D i) ≤ ⊤)
        (le_top : (⨅ i ∈ u.1, π ⁻¹ᵁ D i) ≤ ⊤) e0 (preimage_biInf D π u.1).ge ((1 : R') ⊗ₜ s0)
      rw [LinearMap.baseChange_tmul, SecOnR.baseChangeHom_tmul, SecOnR.baseChangeHom_tmul, one_smul,
        one_smul] at h1
      have h2 := secCubeBaseChange_app_tmul M D H.w u.1 (1 : R') (SecOnR.restrict f M le_top s0)
      rw [one_smul] at h2
      erw [← h1, ← h2]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hbij := termMap_bijOn hM H hD
  constructor
  · intro x y hxy
    apply hflat
    have hx : toC.baseChange R' x ∈ LinearMap.ker (((cechLB f M D).d 0 1).hom.baseChange R') :=
      LinearMap.mem_ker.mpr (hexR.apply_apply_eq_zero x)
    have hy : toC.baseChange R' y ∈ LinearMap.ker (((cechLB f M D).d 0 1).hom.baseChange R') :=
      LinearMap.mem_ker.mpr (hexR.apply_apply_eq_zero y)
    exact hbij.injOn hx hy (by rw [← compat, ← compat, hxy])
  · intro z
    have hz : toC' z ∈ LinearMap.ker ((cechLB f' (M.pull π) fun k => π ⁻¹ᵁ D k).d 0 1).hom :=
      LinearMap.mem_ker.mpr (hex'.apply_apply_eq_zero z)
    obtain ⟨u, hu, hu'⟩ := hbij.surjOn hz
    obtain ⟨x, rfl⟩ := (hexR u).mp (LinearMap.mem_ker.mp hu)
    exact ⟨x, hinj' (by rw [compat, hu'])⟩

theorem eq_smul_iff (x y : SecOnR f M ⊤) (a : R) : x = a • y ↔
    ∀ i, (SecOnR.topEquiv f M x).f i = cst f _ a * (SecOnR.topEquiv f M y).f i := by
  have key : ∀ i, (SecOnR.topEquiv f M (a • y)).f i = cst f (M.U i) a * (SecOnR.topEquiv f M y).f i := by
    intro i
    have hs : a • y = (cst f ⊤ a) • y := rfl
    rw [hs, LinearEquiv.map_smul, ← rs_cst f (le_top : M.U i ≤ ⊤)]
    rfl
  have hext : ∀ (σ τ : LB.Sec M), (∀ i, σ.f i = τ.f i) → σ = τ := by
    rintro ⟨σf, _⟩ ⟨τf, _⟩ hh
    have : σf = τf := funext hh
    subst this
    rfl
  constructor
  · rintro rfl i
    exact key i
  · intro h
    apply (SecOnR.topEquiv f M).injective
    exact hext _ _ (fun i => (h i).trans (key i).symm)

theorem existsUnique_mul_pull [Module.Flat R R'] [CompactSpace Y] [IsSeparated f] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (θ : LB.Sec M)
    (hθ : ∀ σ : LB.Sec M, ∃! a : R, ∀ i, σ.f i = cst f _ a * θ.f i) (σ : LB.Sec (M.pull π)) :
    ∃! a : R', ∀ i, σ.f i = cst f' _ a * (Formalism.L2.Pj.thfPull M π θ).f i := by
  have e0 : (⊤ : Y'.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  have hext : ∀ (σ τ : LB.Sec (M.pull π)), (∀ i, σ.f i = τ.f i) → σ = τ := by
    rintro ⟨σf, _⟩ ⟨τf, _⟩ hh
    have : σf = τf := funext hh
    subst this
    rfl
  have hK : SecOnR.topEquiv f' (M.pull π) (SecOnR.pull M H.w ⊤ ⊤ e0 ((SecOnR.topEquiv f M).symm θ)) =
      Formalism.L2.Pj.thfPull M π θ := by
    apply hext
    intro J
    unfold Formalism.L2.Pj.thfPull SecOnR.topEquiv SecOnR.of SecOn.topEquiv LB.globalEquiv SecOnR.pull
    simp only [LinearEquiv.trans_apply, LinearEquiv.coe_mk]
    change (Y'.presheaf.map (homOfLE _).op).hom ((Y'.presheaf.map (homOfLE _).op).hom
      ((π.appLE _ _ _).hom ((Y.presheaf.map (homOfLE _).op).hom (θ.f (J PUnit.unit))))) = _
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
    have gen : ∀ (U U' : Y.Opens) (V V₁ V₂ : Y'.Opens) (i : Opposite.op U' ⟶ Opposite.op U)
        (e : V ≤ π ⁻¹ᵁ U) (i2 : Opposite.op V ⟶ Opposite.op V₁) (i3 : Opposite.op V₁ ⟶ Opposite.op V₂)
        (e' : V₂ ≤ π ⁻¹ᵁ U'),
        Y.presheaf.map i ≫ π.appLE U V e ≫ Y'.presheaf.map i2 ≫ Y'.presheaf.map i3 = π.appLE U' V₂ e' := by
      intros
      rw [Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    exact congrArg (fun g : Γ(Y, M.U (J PUnit.unit)) ⟶ Γ(Y', (M.pull π).U J) => g.hom (θ.f (J PUnit.unit)))
      (gen _ _ _ _ _ _ _ _ _ _)
  have hB : Function.Bijective (SecOnR.baseChangeHom M H.w ⊤ ⊤ e0) := baseChangeHom_top_bijective hM H
  have hsec : Function.Bijective (LinearMap.toSpanSingleton R (SecOnR f M ⊤) ((SecOnR.topEquiv f M).symm θ)) := by
    constructor
    · intro a b hab
      simp only [LinearMap.toSpanSingleton_apply] at hab
      obtain ⟨c, -, hc⟩ := hθ (SecOnR.topEquiv f M (a • (SecOnR.topEquiv f M).symm θ))
      have ha := (eq_smul_iff (a • (SecOnR.topEquiv f M).symm θ) ((SecOnR.topEquiv f M).symm θ) a).mp rfl
      have hb := (eq_smul_iff (a • (SecOnR.topEquiv f M).symm θ) ((SecOnR.topEquiv f M).symm θ) b).mp hab
      rw [LinearEquiv.apply_symm_apply] at ha hb
      exact (hc a ha).trans (hc b hb).symm
    · intro s
      obtain ⟨a, ha, -⟩ := hθ (SecOnR.topEquiv f M s)
      refine ⟨a, ?_⟩
      rw [LinearMap.toSpanSingleton_apply]
      refine ((eq_smul_iff s ((SecOnR.topEquiv f M).symm θ) a).mpr ?_).symm
      rw [LinearEquiv.apply_symm_apply]
      exact ha
  let φL := LinearEquiv.ofBijective _ hsec
  let Φ : R' → SecOnR f' (M.pull π) ⊤ := fun c =>
    SecOnR.baseChangeHom M H.w ⊤ ⊤ e0 (LinearEquiv.lTensor R' φL ((TensorProduct.rid R R').symm c))
  have hΦ : Function.Bijective Φ :=
    hB.comp ((LinearEquiv.lTensor R' φL).bijective.comp (TensorProduct.rid R R').symm.bijective)
  have hΦc : ∀ c, Φ c = c • SecOnR.pull M H.w ⊤ ⊤ e0 ((SecOnR.topEquiv f M).symm θ) := by
    intro c
    simp only [Φ, TensorProduct.rid_symm_apply, LinearEquiv.lTensor_tmul, φL, LinearEquiv.ofBijective_apply,
      LinearMap.toSpanSingleton_apply, one_smul, SecOnR.baseChangeHom_tmul]
  have key : ∀ c : R', (SecOnR.topEquiv f' (M.pull π)).symm σ =
      c • SecOnR.pull M H.w ⊤ ⊤ e0 ((SecOnR.topEquiv f M).symm θ) ↔
      ∀ i, σ.f i = cst f' _ c * (Formalism.L2.Pj.thfPull M π θ).f i := by
    intro c
    rw [eq_smul_iff, LinearEquiv.apply_symm_apply, hK]
  obtain ⟨c, hc⟩ := hΦ.2 ((SecOnR.topEquiv f' (M.pull π)).symm σ)
  refine ⟨c, (key c).mp (by rw [← hc, hΦc]), fun c' hc' => hΦ.1 ?_⟩
  rw [hΦc, hΦc, ← (key c').mpr hc', ← hc, hΦc]

open Geo.Tor Formalism.L2.Pj in

theorem existsUnique_mul_of_isoMaps {L' : LB Y'} (hM : M.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (M.pull π)}
    (hw : w.IsGen) (θ' : LB.Sec L') (θ : LB.Sec (M.pull π)) (h : IsoMaps w θ' θ)
    (hθ : ∀ σ : LB.Sec (M.pull π), ∃! a : R', ∀ i, σ.f i = constFn f' _ a * θ.f i) (σ' : LB.Sec L') :
    ∃! a : R', ∀ i, σ'.f i = constFn f' _ a * θ'.f i := by
  classical
  have unitCancel1 : ∀ {S : Type} [CommRing S] (u : Sˣ) (c a b x y : S), x = c * y → y = ↑u * b →
      x = ↑u * a → a = c * b := by
    intro S _ u c a b x y h1 h2 h3
    calc a = ↑u⁻¹ * (↑u * a) := (Units.inv_mul_cancel_left u a).symm
      _ = ↑u⁻¹ * (c * (↑u * b)) := by rw [← h3, h1, h2]
      _ = c * b := by rw [mul_left_comm, Units.inv_mul_cancel_left]
  have unitCancel2 : ∀ {S : Type} [CommRing S] (u : Sˣ) (c a b x y : S), a = c * b → y = ↑u * b →
      x = ↑u * a → x = c * y := by
    intro S _ u c a b x y h1 h2 h3
    rw [h3, h1, h2, mul_left_comm]
  have hMp : (M.pull π).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hM π
  obtain ⟨w', hw', hinv⟩ := GlobalTheory.GenericSectionBasis.exists_inv_iso w hw
  set σ : LB.Sec (M.pull π) := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso σ' hw' hMp hL' with hσdef
  have hrel : ∀ (y : Y') (J : (M.pull π).ι) (k : L'.ι), y ∈ (M.pull π).U J → y ∈ L'.U k →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 Y') y _ (σ.f J) =
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gw w (𝟙 Y') y (J PUnit.unit) k).val *
            ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 Y') y _ (σ'.f k) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 Y') y _ (θ.f J) =
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gw w (𝟙 Y') y (J PUnit.unit) k).val *
            ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 Y') y _ (θ'.f k) := by
    intro y J k hJ hk
    constructor
    · have hs := GlobalTheory.GenericGenerated.gs_secOfIso w' σ' hw' hMp hL' J k (𝟙 Y') y
        (TopologicalSpace.Opens.mem_inf.2 ⟨hJ, hk⟩)
      rw [hinv Y' (𝟙 Y') y k J (TopologicalSpace.Opens.mem_inf.2 ⟨hk, hJ⟩), inv_inv] at hs
      exact hs
    · exact (GlobalTheory.ArcQ.FrUniq.isoMaps_iff w θ' θ).mp h Y' (𝟙 Y') y (J PUnit.unit) k
        ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull).mp hJ) hk
  obtain ⟨a, ha, huniq⟩ := hθ σ
  have haP := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_eq_iff f' σ θ a).mp ha
  refine ⟨a, ?_, ?_⟩
  · refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_eq_iff f' σ' θ' a).mpr ?_
    intro k y hk
    obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hM (π y)
    have hJ : y ∈ (M.pull π).U (fun _ => j) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull).mpr hj
    obtain ⟨h3, h2⟩ := hrel y (fun _ => j) k hJ hk
    exact unitCancel1 _ _ _ _ _ _ (haP (fun _ => j) y hJ) h2 h3
  · intro b hb
    have hbP := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_eq_iff f' σ' θ' b).mp hb
    apply huniq
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_eq_iff f' σ θ b).mpr ?_
    intro J y hJ
    obtain ⟨k, hk⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL' y
    obtain ⟨h3, h2⟩ := hrel y J k hJ hk
    exact unitCancel2 _ _ _ _ _ _ (hbP k y hk) h2 h3

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
  have isTan_iff : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (w : epsOver R R ⟶ G),
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan w ↔ IsTan w := by
    intro R _ G _ w
    unfold ReciprocityTheory.ChartRestriction.G.Chart.IsTan IsTan
    constructor
    · intro h
      exact congrArg (fun q => Over.Hom.left q) h
    · intro h
      exact Over.OverMorphism.ext h
  have prod_tvec : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
      {x : ∀ k : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) k) ⟶ G}
      (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart G n x) {m : ℕ} (c : Fin m → R) (b : Fin m → Fin n → R),
      (List.ofFn fun i => tvec (x := x) (c i • b i)).prod = tvec (x := x) (∑ i, c i • b i) := by
    intro R _ G _ n x hx m c b
    obtain ⟨h, hh⟩ := ReciprocityTheory.ChartRestriction.G.Chart.list_prod_tan' hx (fun i => tvec (x := x) (c i • b i))
      (fun i => isTan_tvec hx _)
    calc (List.ofFn fun i => tvec (x := x) (c i • b i)).prod
        = tvec (x := x) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ h) := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx _ h
      _ = tvec (x := x) (∑ i, c i • b i) := by
        rw [hh]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => ReciprocityTheory.ChartRestriction.G.Chart.tcoord_tvec hx _)
  have comb_iff : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
      {x : ∀ k : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) k) ⟶ G}
      (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart G n x) {m : ℕ} (b : Fin m → Fin n → R) (c : Fin m → R)
      (w : epsOver R R ⟶ G),
      IsComb (fun i => tvec (x := x) (b i)) c w ↔ w = tvec (x := x) (∑ i, c i • b i) := by
    intro R _ G _ n x hx m b c w
    have hs : ∀ i, tvec (x := x) (c i • b i) =
        ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (c i)) ≫ tvec (x := x) (b i) :=
      fun i => ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx (c i) (b i)
    constructor
    · rintro ⟨u', hu', rfl⟩
      have e : u' = fun i => tvec (x := x) (c i • b i) := by
        funext i
        apply Over.OverMorphism.ext
        rw [hu' i, hs i]
        rfl
      subst e
      exact prod_tvec hx c b
    · intro hw
      refine ⟨fun i => tvec (x := x) (c i • b i), fun i => ?_, ?_⟩
      · dsimp only
        rw [hs i]
        rfl
      · rw [hw, prod_tvec hx c b]
  have eig_iff : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
      {x : ∀ k : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) k) ⟶ G}
      (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart G n x) (f : G ⟶ G) [IsMonHom f] (c : Fin n → R) (s : R),
      (tvec (x := x) c ≫ f).left = spMap (epsMul s) ≫ (tvec (x := x) c).left ↔ tmap hx f c = s • c := by
    intro R _ G _ n x hx f _ c s
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff hx f c s]
    constructor
    · intro h
      exact Over.OverMorphism.ext h
    · intro h
      exact congrArg (fun q => Over.Hom.left q) h
  have vecMul_eq : ∀ {A S : Type} [CommRing A] [CommRing S] [Algebra A S] {d : ℕ}
      (L : (Fin d → A) →ₗ[A] (Fin d → A)) (T : (Fin d → S) →ₗ[S] (Fin d → S)),
      (∀ c, T (algebraMap A S ∘ c) = algebraMap A S ∘ L c) → ∀ (w : Fin d → S),
      w ᵥ* (Matrix.of fun i k => L (fun j => if i = j then 1 else 0) k).map (algebraMap A S) = T w := by
    intro A S _ _ _ d L T hT w
    rw [LinearMap.pi_apply_eq_sum_univ T w]
    funext k
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e : (fun j => if i = j then (1 : S) else 0) = algebraMap A S ∘ (fun j => if i = j then (1 : A) else 0) := by
      funext j
      by_cases h : i = j <;> simp [h]
    rw [e, hT]
    rfl
  obtain ⟨d, x, hx⟩ := univChartLoc G
  obtain ⟨x', hx', hxx'⟩ := tanBC_alg (R' := V') G d x hx
  have htan : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (u i) := fun i => (isTan_iff (u i)).2 (ht i)
  obtain ⟨b, hu⟩ : ∃ b : Fin m → Fin d → V, u = fun i => tvec (x := x) (b i) :=
    ⟨fun i => ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx (u i) (htan i),
      funext fun i => ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx (u i) (htan i)⟩
  subst hu
  have hbe : ∀ i a, tmap hx (act a) (b i) = χ a • b i :=
    fun i a => (eig_iff hx (act a) (b i) (χ a)).1 (he i a)
  let M : O → Matrix (Fin d) (Fin d) V :=
    fun a => Matrix.of fun i k => tmap hx (act a) (fun j => if i = j then 1 else 0) k
  have hMV : ∀ a (w : Fin d → V), w ᵥ* (M a).map (algebraMap V V) = tmap hx (act a) w :=
    fun a w => vecMul_eq (tmap hx (act a)) (tmap hx (act a)) (fun c => by ext; simp) w
  have hM0 : ∀ a (w : Fin d → V), w ᵥ* M a = tmap hx (act a) w := by
    intro a w
    have e : (M a).map (algebraMap V V) = M a := by
      ext i k
      rfl
    rw [← e]
    exact hMV a w
  have key := (GlobalTheory.commonEigenvectors_flat_baseChange V O d m M χ).1 V b
    (fun k a => (hM0 a (b k)).trans (hbe k a))
    (fun w hw => by
      have hw' : ∀ a, tmap hx (act a) w = χ a • w := fun a => (hMV a w).symm.trans (hw a)
      obtain ⟨c, hc, huniq⟩ := hb (tvec (x := x) w) ((isTan_iff _).1 (isTan_tvec hx w))
        (fun a => (eig_iff hx (act a) w (χ a)).2 (hw' a))
      refine ⟨c, ?_, fun c' hc' => huniq c' ?_⟩
      · exact tvec_inj hx ((comb_iff hx b c _).1 hc)
      · exact (comb_iff hx b c' _).2 (congrArg (fun z => tvec (x := x) z) hc'))
  have hT : ∀ a c, tmap hx' ((Over.pullback (fB V V')).map (act a)) (algebraMap V V' ∘ c) =
      algebraMap V V' ∘ tmap hx (act a) c := by
    intro a c
    apply tvec_inj hx'
    rw [tvec_tmap hx' ((Over.pullback (fB V V')).map (act a))]
    apply pushR_inj G
    apply Over.OverMorphism.ext
    rw [pushR_map, Over.comp_left, pushR_left, pushR_left, hxx' c, hxx' (tmap hx (act a) c),
      tvec_tmap hx (act a) c, Over.comp_left, Category.assoc]
  have hbe' : ∀ i a, tmap hx' ((Over.pullback (fB V V')).map (act a)) (algebraMap V V' ∘ b i) =
      algebraMap V V' (χ a) • (algebraMap V V' ∘ b i) := by
    intro i a
    rw [hT, hbe i a]
    funext j
    simp
  refine ⟨fun i => tvec (x := x') (algebraMap V V' ∘ b i), fun i => (isTan_iff _).1 (isTan_tvec hx' _),
    fun i a => (eig_iff hx' _ _ _).2 (hbe' i a), ?_, fun i => hxx' (b i)⟩
  intro w hw hwe
  have hwc := (isTan_iff w).2 hw
  obtain ⟨c', rfl⟩ : ∃ c', w = tvec (x := x') c' := ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx' w hwc⟩
  have hce : ∀ a, tmap hx' ((Over.pullback (fB V V')).map (act a)) c' = algebraMap V V' (χ a) • c' :=
    fun a => (eig_iff hx' _ c' _).1 (hwe a)
  have hk := key V' c' (fun a => (vecMul_eq (tmap hx (act a))
    (tmap hx' ((Over.pullback (fB V V')).map (act a))) (hT a) c').trans (hce a))
  refine (existsUnique_congr fun cf => ?_).2 hk
  rw [comb_iff hx' (fun i => algebraMap V V' ∘ b i) cf]
  constructor
  · intro h
    exact tvec_inj hx' h
  · intro h
    exact congrArg (fun z => tvec (x := x') z) h

end Lie

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_restrict (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ)
    (h : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) :
    ∃ φ : T.V →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a) := by
  classical
  have key : ∀ a : T.V, iT (algebraMap T.V T.Fr a) ∈ (algebraMap T'.V T'.Fr).range := by
    intro a
    by_cases hx : iT (algebraMap T.V T.Fr a) = 0
    · rw [hx]; exact zero_mem _
    have ha : algebraMap T.V T.Fr a ≠ 0 := fun h0 => hx (by rw [h0, map_zero])
    have h1 := h (algebraMap T.V T.Fr a)
    unfold vV valV at h1
    have hle : (IsDiscreteValuationRing.maximalIdeal T.V).valuation (FractionRing T.V)
        (algebraMap T.V T.Fr a) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := FractionRing T.V) a
    have hne : (IsDiscreteValuationRing.maximalIdeal T.V).valuation (FractionRing T.V)
        (algebraMap T.V T.Fr a) ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
    have hne' : (IsDiscreteValuationRing.maximalIdeal T'.V).valuation (FractionRing T'.V)
        (iT (algebraMap T.V T.Fr a)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    have hlog : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation (FractionRing T.V)
        (algebraMap T.V T.Fr a)) ≤ 0 := (WithZero.log_le_iff_le_exp hne).mpr hle
    have hpos : (0 : ℤ) ≤ (e : ℤ) * -WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation
        (FractionRing T.V) (algebraMap T.V T.Fr a)) :=
      mul_nonneg (Int.natCast_nonneg e) (neg_nonneg.mpr hlog)
    have hlog' : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T'.V).valuation (FractionRing T'.V)
        (iT (algebraMap T.V T.Fr a))) ≤ 0 := by linarith
    have hle' := (WithZero.log_le_iff_le_exp hne').mp hlog'
    obtain ⟨b, hb⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := T'.V) (K := FractionRing T'.V) hle'
    exact ⟨b, hb⟩
  let g : T'.V →+* (algebraMap T'.V T'.Fr).range := (algebraMap T'.V T'.Fr).rangeRestrict
  have hg : Function.Bijective g :=
    ⟨fun x y hxy => IsFractionRing.injective T'.V T'.Fr (congrArg Subtype.val hxy),
      (algebraMap T'.V T'.Fr).rangeRestrict_surjective⟩
  let eq := RingEquiv.ofBijective g hg
  refine ⟨eq.symm.toRingHom.comp ((iT.comp (algebraMap T.V T.Fr)).codRestrict _ key), fun a => ?_⟩
  have h2 : g (eq.symm ⟨_, key a⟩) = ⟨_, key a⟩ := eq.apply_symm_apply _
  exact congrArg Subtype.val h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

open GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique in

theorem integral_of_frMap (T T' : CDVR) (io : c.F →+* T.Fr) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V)
    (hφ : ∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) :
    letI := io.toAlgebra
    letI := (iT.comp io).toAlgebra
    ∀ (ψ : T.Fr →ₐ[c.F] T'.Fr) (y : FrPt Xo c T.Fr) (y' : FrPt Xo c T'.Fr), ψ.toRingHom = iT → FrMap ψ y y' →
      Integral T io y → Integral T' (iT.comp io) y' := by
  intro ψ y y' hψ hm hy
  letI : Algebra c.F T.Fr := io.toAlgebra
  letI : Algebra c.F T'.Fr := (iT.comp io).toAlgebra
  have isoSec : ∀ {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {F : Y ⟶ X} (w : LB.Iso L' (L.pull F))
      (hw : w.IsGen) (hA : L'.IsLB) (hB : (L.pull F).IsLB) (s : LB.Sec (L.pull F)),
      IsoMaps w (ReciprocityTheory.ChartRestriction.G.DVR.secOfIso s hw hA hB) s := by
    intro X Y L L' F w hw hA hB s i k
    have e := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec s hw hA hB k i
    have hV : (L.pull F).U i ⊓ L'.U k ≤ L'.U k ⊓ (L.pull F).U i := le_of_eq (inf_comm _ _)
    have e2 := congrArg (ReciprocityTheory.ChartRestriction.G.DVR.rs hV) e
    unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand at e2
    unfold ReciprocityTheory.ChartRestriction.G.Semi.res at e2
    unfold ReciprocityTheory.ChartRestriction.G.DVR.rs at e2
    have hcomp : ∀ {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(Y, U)),
        (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom a) =
          (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
      intro U V W h1 h2 a
      change (Y.presheaf.map (homOfLE h1).op ≫ Y.presheaf.map (homOfLE h2).op).hom a = _
      rw [← Functor.map_comp]
      rfl
    have hid : ∀ {U : Y.Opens} (h : U ≤ U) (a : Γ(Y, U)), (Y.presheaf.map (homOfLE h).op).hom a = a := by
      intro U h a
      change (Y.presheaf.map (𝟙 (Opposite.op U))).hom a = a
      rw [CategoryTheory.Functor.map_id]
      rfl
    simp only [map_mul, Units.coe_map_inv, MonoidHom.coe_coe, hcomp] at e2
    erw [hid] at e2
    rw [e2]
    exact (Units.mul_inv_cancel_left (w.s (i, k)) _).symm
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hlift⟩, θ, hθ, htie⟩ := hy
  have hsq : (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) := RingHom.ext hφ
  have hsqS : spMap (algebraMap T'.V T'.Fr) ≫ spMap φ = spMap iT ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.FramedBaseChange.spMap_spMap, GlobalTheory.FramedBaseChange.spMap_spMap, hsq]
  have hcast : ∀ {S' S : Scheme.{0}} {t₁ : SAB H S'} {t₂ : SAB H S} {f g : S' ⟶ S} (h : f = g) (m : SABMap t₁ t₂ f),
      ∃ m' : SABMap t₁ t₂ g, m'.φ = m.φ := by
    intro S' S t₁ t₂ f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨PP', cub', sym', adj', prim', n2, hn2⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
  let G' := (fun {t : SAB H (Sp T'.V)} (_ : SABMap t G (spMap φ)) => t) n2
  obtain ⟨PP'', cub'', sym'', adj'', prim'', m2', hm2'⟩ :=
    sabPull Out.CubePf.cubePull (spMap (algebraMap T'.V T'.Fr)) G'
  let t'' := (fun {t : SAB H (Sp T'.Fr)} (_ : SABMap t G' (spMap (algebraMap T'.V T'.Fr))) => t) m2'
  obtain ⟨k, hk⟩ := sabComp pullCubComp E H _ _ _ G G' t'' (spMap φ) (spMap (algebraMap T'.V T'.Fr)) n2 m2'
  obtain ⟨k', hk'⟩ := hcast hsqS k
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ G t' t'' (spMap (algebraMap T.V T.Fr)) (spMap iT) m2 k'
  have hx' : spMap iT ≫ y.x = y'.x := by rw [hm.1, hψ]
  obtain ⟨m1c, hm1c⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t t' t'' y.x (spMap iT) m1 n
  obtain ⟨m1', hm1'⟩ := hcast hx' m1c
  have hφinj : Function.Injective φ := by
    intro a b h
    apply IsFractionRing.injective T.V T.Fr
    apply iT.injective
    rw [← hφ, ← hφ, h]
  letI : Algebra T.V T'.V := φ.toAlgebra
  haveI : Module.IsTorsionFree T.V T'.V := ⟨fun r hr a b hab => by
    have hr0 : φ r ≠ 0 := fun h0 => hr.ne_zero (hφinj (by rw [h0, map_zero]))
    exact mul_left_cancel₀ hr0 hab⟩
  haveI : Module.Flat T.V T'.V := inferInstance
  obtain ⟨_, hsm, hsep, hqc, -, -⟩ := G.semi
  have hχ : ∀ (τ : E →+* ℂ) (a : 𝓞 E), ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ a) :=
    fun τ a => int_val (c := c) T io τ a
  choose χ hχ using hχ
  haveI : ∀ a, IsMonHom (G.act.act a) := G.act.hom
  have hLie := fun τ => exists_eigenbasis_pullback (V' := T'.V) G.G (fun a => G.act.act a) (χ τ) (ub τ) (htan τ)
    (fun i a => heig τ i a (χ τ a) (hχ τ a))
    (fun w hw he => hbas τ w hw (fun a z hz => by
      have hz' : z = χ τ a := IsFractionRing.injective T.V T.Fr (by rw [hz, hχ])
      rw [hz']
      exact he a))
  choose ub' htan' heig' hbas' hpr' using hLie
  have hpr'' : ∀ τ i, (ub' τ i).left ≫ pullback.fst G.G.hom (spMap φ) = spMap (dualMap φ) ≫ (ub τ i).left :=
    hpr'
  have hmono : Mono (spMap (algebraMap T.V T.Fr)) := by
    haveI : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
    exact Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap T.V T.Fr)).op
  have hlift' : ∀ τ i, ∃ u'' : Sp (DualNumber T'.Fr) ⟶ t''.G.left, u'' ≫ m1'.φ = y'.u τ i ∧
      u'' ≫ m2'.φ = spMap (dualMap (algebraMap T'.V T'.Fr)) ≫ (ub' τ i).left := by
    intro τ i
    obtain ⟨u0, hu1, hu2⟩ := hlift τ i
    have hw : (spMap (dualMap (algebraMap T'.V T'.Fr)) ≫ (ub' τ i).left) ≫ G'.G.hom =
        spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap (algebraMap T'.V T'.Fr) := by
      rw [Category.assoc, Over.w (ub' τ i), GlobalTheory.Reg.ChartInhab.eps_hom, GlobalTheory.ArcQ.FrBC.dual_alg]
    have hb0 : u0 ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      apply (cancel_mono (spMap (algebraMap T.V T.Fr))).1
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub τ i),
        GlobalTheory.Reg.ChartInhab.eps_hom, GlobalTheory.ArcQ.FrBC.dual_alg]
    have hkey : m2'.cart.1.lift _ _ hw ≫ n.φ = spMap (dualMap iT) ≫ u0 := by
      apply m2.cart.1.hom_ext
      · rw [Category.assoc, ← hn, hk', hk, ← Category.assoc, m2'.cart.1.lift_fst, Category.assoc, hn2,
          hpr'' τ i, Category.assoc, hu2, ← Category.assoc, ← Category.assoc, ← GlobalTheory.ArcQ.FrBC.dual_comp,
          ← GlobalTheory.ArcQ.FrBC.dual_comp, hsq]
      · rw [Category.assoc, n.cart.1.w, ← Category.assoc, m2'.cart.1.lift_snd, Category.assoc, hb0,
          GlobalTheory.ArcQ.FrBC.dual_alg]
    refine ⟨m2'.cart.1.lift _ _ hw, ?_, m2'.cart.1.lift_fst _ _ _⟩
    rw [hm1', hm1c, ← Category.assoc, hkey, Category.assoc, hu1, hm.2.1 τ i, hψ]
  unfold Integral
  refine ⟨G', t'', m1', m2', ⟨ub', htan', fun τ i a z hz => ?_, fun τ w hw he => ?_, hlift'⟩, ?_⟩
  · have hz' : z = φ (χ τ a) := IsFractionRing.injective T'.V T'.Fr (by rw [hz, hφ, hχ]; rfl)
    rw [hz']
    exact heig' τ i a
  · exact hbas' τ w hw (fun a => he a (φ (χ τ a)) (by rw [hφ, hχ]; rfl))
  · obtain ⟨wn, hwn⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso n2
    letI : GrpObj ((Over.pullback (spMap φ)).obj G.G) := G'.grp
    have hAlb := G'.PP.isLB
    have hBlb := pull_isLB G.PP.isLB n2.φ
    let θ' := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (thfPull G.PP.L n2.φ θ) hwn.1 hAlb hBlb
    have hiso : IsoMaps wn θ' (thfPull G.PP.L n2.φ θ) := isoSec wn hwn.1 hAlb hBlb _
    have hT : GlobalTheory.ArcQ.FrUniq.Comparison₂ m1 m2 θ y.s := (GlobalTheory.ArcQ.FrUniq.tie_iff m1 m2 θ y.s).1 htie
    obtain ⟨-, -, pm, hps, hpb, hpm⟩ := hm
    have hT' : GlobalTheory.ArcQ.FrUniq.Comparison₂ m1' k' θ y'.s := by
      refine GlobalTheory.ArcQ.FrUniq.tie_pull m1 m2 θ y.s n m1' k' hx'.symm rfl (hm1'.trans hm1c) hn y'.s pm hps
        (by rw [hpb, hψ]) (fun Z r z j hz => ?_) hT
      rw [← hpm (fun _ => j) (GlobalTheory.FramedBaseChange.chart_le pm hps _)]
      exact GlobalTheory.EndDivisible.gs_appLE r pm z _ _ _ hz _
    obtain ⟨w1, wk, σ, hr1, hrk, hsec, hpt⟩ := hT'
    obtain ⟨θk, hθk, hik⟩ := (GlobalTheory.ArcQBC.through_iff (w := wk) θ σ).2
      (fun z j kk hj hk => hpt _ (𝟙 _) z j kk hj hk)
    obtain ⟨w', hw', hi'⟩ := GlobalTheory.ArcQ.FrBC.exists_isoMaps_cancel n2 m2' k' hsqS.symm (hk'.trans hk) hwn hrk
      hiso (fun _ _ => rfl) hik hθk
    refine ⟨θ', ?_, (GlobalTheory.ArcQ.FrUniq.tie_iff m1' m2' θ' y'.s).2 ⟨w1, w', σ, hr1, hw', hsec,
      fun Z r z j kk hj hk => GlobalTheory.ArcQ.FrBC.gs_of_isoMaps hi' (fun _ _ => rfl) r z j kk hj hk⟩⟩
    intro σ''
    haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
    have hgen := existsUnique_mul_pull (f := G.G.hom) (f' := G'.G.hom) (π := n2.φ) G.PP.isLB n2.cart.1 θ
      (fun σ => hθ σ)
    exact existsUnique_mul_of_isoMaps (f' := G'.G.hom) G.PP.isLB hAlb hwn.1 θ' _ hiso hgen σ''

end Main

end GlobalTheory.ThetaBound.Ext

namespace GlobalTheory.ThetaBound

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem exists_isExt_and_trans : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e : ℕ), 0 < e → (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) → (∃ y' : IntFr Xo c T' (iT.comp io), IsExt y iT e y') ∧ ∀ y' : IntFr Xo c T' (iT.comp io), IsExt y iT e y' → xOf y' = spMap iT ≫ xOf y ∧ ∀ (T'' : CDVR) (iT' : T'.Fr →+* T''.Fr) (e' : ℕ) (y'' : IntFr Xo c T'' (iT'.comp (iT.comp io))), IsExt y' iT' e' y'' → IsExt y (iT'.comp iT) (e' * e) y'' := by
  intro E _ _ _ H Dw l Xo c T T' io y iT e he hv
  letI : Algebra c.F T.Fr := io.toAlgebra
  letI : Algebra c.F T'.Fr := (iT.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { iT with commutes' := fun _ => rfl }
  have hψ : ψ.toRingHom = iT := rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨φ, hφ⟩ := Ext.exists_restrict T T' iT e hv
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.allSixLaws.1 E H Dw l Xo c T.Fr T'.Fr ψ y.1
    obtain ⟨p, φ0, y0, h0⟩ := y.2.1
    exact ⟨⟨z, ⟨p, ψ.comp φ0, y0, GlobalTheory.FramedBaseChange.trans φ0 ψ h0 hz⟩,
      Ext.integral_of_frMap T T' io iT φ hφ ψ y.1 z hψ hz y.2.2⟩, he, hv, ψ, hψ, hz⟩
  · intro y' hy'
    obtain ⟨_, _, φ1, hφ1, hm1⟩ := hy'
    refine ⟨?_, ?_⟩
    · show y'.1.x = spMap iT ≫ y.1.x
      rw [hm1.1, hφ1]
    · intro T'' iT' e' y'' h2
      letI : Algebra c.F T''.Fr := (iT'.comp (iT.comp io)).toAlgebra
      obtain ⟨he', hv', φ2, hφ2, hm2⟩ := h2
      refine ⟨Nat.mul_pos he' he, fun a => ?_, φ2.comp φ1, ?_, GlobalTheory.FramedBaseChange.trans φ1 φ2 hm1 hm2⟩
      · rw [RingHom.comp_apply, hv', hv a]
        push_cast
        ring
      · ext a
        have h1 := congrArg (fun f : T.Fr →+* T'.Fr => f a) hφ1
        have h2 := congrArg (fun f : T'.Fr →+* T''.Fr => f (iT a)) hφ2
        show φ2 (φ1 a) = iT' (iT a)
        rw [← h2, ← h1]
        rfl

end GlobalTheory.ThetaBound
