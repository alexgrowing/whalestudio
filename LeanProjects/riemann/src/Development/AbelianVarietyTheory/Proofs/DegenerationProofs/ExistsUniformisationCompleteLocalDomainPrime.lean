import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompareUniformisationDataPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegDataPsiOfSectionNonzeroFibresStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnifOfCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformizationDataCompleteLocalPrimeStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PrimeUnif

theorem exists_cdvr (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (I : Ideal R) [I.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V), CDvr V ∧ Function.Injective φ ∧
      (IsLocalRing.maximalIdeal V).comap φ = I := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · let K := FractionRing R
    let φ : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
    have hφ : Function.Injective φ := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, φ,
      ⟨inferInstance, ?_, charZero_of_injective_ringHom hφ⟩, hφ, ?_⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
    · refine eq_bot_iff.2 fun r hr => ?_
      rw [Ideal.mem_comap, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
        PowerSeries.X_dvd_iff] at hr
      have : algebraMap R K r = 0 := by simpa [φ] using hr
      exact (Ideal.mem_bot).2 (IsFractionRing.injective R K (this.trans (map_zero _).symm))
  · obtain ⟨V, _, _, hV, hc, φ, h1, h2⟩ := exists_complete_discreteValuationRing_of_prime_lt ⊥ I (bot_lt_iff_ne_bot.2 hI)
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    exact ⟨V, inferInstance, inferInstance, inferInstance, φ, ⟨hV, hc, charZero_of_injective_ringHom hφ⟩, hφ, h2⟩

theorem isCPMap_of_eq (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] {A : PolAV (Sp (FractionRing V))}
    {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G'] [Smooth G'.hom] (gen : (Over.pullback (jK V)).obj G' ≅ A.A)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : CP G} {f : Sp V ⟶ S} {F : G'.left ⟶ G.left}
    {hw : F ≫ G.hom = G'.hom ≫ f} (P₁ P₂ : CP G') (e : P₂.L = P₁.L) {w} (h : IsCPMap P₁ P f F hw w) :
    ∃ w', IsCPMap P₂ P f F hw w' := by
  obtain ⟨L, c, s, hs, hr, hc⟩ := P₂
  obtain rfl : L = P₁.L := e
  let P₂ : CP G' := ⟨P₁.L, c, s, hs, hr, hc⟩
  have : Flat (G3 G').hom := by
    show Flat (pullback.fst G'.hom (pullback.fst G'.hom G'.hom ≫ G'.hom) ≫ G'.hom)
    infer_instance
  have h1 : Function.Surjective (pullback.snd G'.hom (jK V)).appTop.hom := by
    have hw : gen.hom.left ≫ A.A.hom = pullback.snd G'.hom (jK V) := Over.w gen.hom
    have : IsIso gen.hom.left := ((Over.forget _).mapIso gen).isIso_hom
    have : IsIso gen.hom.left.appTop := inferInstanceAs (IsIso (gen.hom.left.app ⊤))
    rw [← hw]
    exact surj_comp (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2 (hG _ _ A.isAb).2
  let o : Over.mk (jK V) ⟶ G' := 1
  let o₃ : Over.mk (jK V) ⟶ G3 G' := lift o (lift o o)
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (J), Good P₁.L.L z J → val P₁.sym r z J = val s r z J :=
    ValueForm.gen_unique_of_injective P₁.L.isLB (fun _ _ _ => rfl) (pullback.fst G'.hom (jK V))
      (ValueForm.app_generic_injective _) (pullback.snd _ _)
      (pullback.lift o.left (𝟙 _) ((Over.w o).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) h1
      P₁.sym_gen hs fun y J hJ => by
        rw [pullback.lift_fst]
        exact (P₁.val_sym_one hJ).trans (P₂.val_sym_one hJ).symm
  have ec : ∀ (T : Over (Sp V)) (z : T.left) (J), Good P₁.L.L z J → ∀ x y u : T ⟶ G',
      cubV P₁.c z J x y u = cubV c z J x y u := fun T z J hJ x y u =>
    ValueForm.gen_unique_of_injective P₁.L.isLB (φ := thφ G' (x3 G')) (ε := thε) (φ' := thφ G' (x3 G')) (ε' := thε)
      (fun _ _ _ => rfl) (pullback.fst (G3 G').hom (jK V))
      (ValueForm.app_generic_injective _) (pullback.snd _ _)
      (pullback.lift o₃.left (𝟙 _) ((Over.w o₃).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
      (ValueForm.surjective_cube_baseChange hG _ A.isAb gen) P₁.c.isGen c.isGen
      (fun y J hJ => by
        rw [pullback.lift_fst]
        exact ((isCub_cubV P₁.c (T := Over.mk (jK V)) hJ).face 1 1).trans
          ((isCub_cubV c (T := Over.mk (jK V)) hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨w, h.mul, h.gen, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨a₁, a₂, a₃⟩ := h.vals T z J' J hJ' hJ W hW
  exact ⟨a₁, fun x => (a₂ x).trans (congrArg (W x⁻¹ * ·) (es _ x.left z J' hJ')),
    fun x y u => (a₃ x y u).trans (congrArg (W (x * y * u) * W x * W y * W u * ·) (ec T z J' hJ' x y u))⟩

section Psi
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
  [IsCommMonObj G']
  (psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)))
  (h : ∀ χ, (psi χ).IsGen)

def gtWithPsi {e : ℕ} (g : GtCoord I D e G) : GtCoord I (withPsi D psi h) e G :=
  ⟨g.q, g.q_hom, g.q_flat, g.q_surj, g.q_affine, g.i, g.i_hom, g.isKernel, g.t, g.t_gen, g.t_mul, g.t_unit, g.t_weight⟩

def preWithPsi (U : PreU I D A G) : PreU I (withPsi D psi h) A G :=
  ⟨U.semi, U.gen, U.gen_hom, U.P, U.wA, U.wA_gen, fun e => gtWithPsi psi h (U.gt e), U.gt_q, U.gt_t, U.w, U.w_gen,
    U.w_vals, U.w_compat⟩

def cmpWithPsi {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left} (C : Cmp φ U U' F) :
    Cmp φ (preWithPsi psi h U) U' F :=
  ⟨C.pb, C.wL, C.wL_map, C.β, C.pbB, C.v, C.v_gen, C.xe, C.c_pr, C.lev, C.map_le⟩

theorem exists_move {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left} (C : Cmp φ U U' F)
    (hD : IsPullDeg φ (withPsi D psi h) D') (D₂ : DegPre R) (e : D₂ = withPsi D psi h)
    (h₁ : hD.e.hom.left ≫ pullback.fst _ _ = C.β) (h₂ : HEq hD.w C.v) (h₃ : hD.xe = C.xe) :
    ∃ (U₂ : PreU I D₂ A G) (C₂ : Cmp φ U₂ U' F) (hD₂ : IsPullDeg φ D₂ D'), U₂.P = U.P ∧ U₂.gen = U.gen ∧
      hD₂.e.hom.left ≫ pullback.fst _ _ = C₂.β ∧ HEq hD₂.w C₂.v ∧ hD₂.xe = C₂.xe := by
  subst e
  exact ⟨preWithPsi psi h U, cmpWithPsi psi h C, hD, rfl, rfl, h₁, h₂, h₃⟩

end Psi

set_option maxHeartbeats 1600000 in

theorem exists_setting (hL : Laws) (hL2 : Laws2) (hL3 : Laws3) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G)
    (hW : HypW G P.L.L) (hsp : SplitOver G I) (A : PolAV (Sp (FractionRing R)))
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (g : R →+* V) (hg : Function.Injective g)
    (hI : I ≤ (IsLocalRing.maximalIdeal V).comap g) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap g)).obj G)) (w : _),
      IsCPMap s.P P (spMap g) (pullback.fst G.hom (spMap g)) pullback.condition w := by
  let G' : Over (Sp V) := (Over.pullback (spMap g)).obj G
  have pb : IsGrpPullback G' G (spMap g) (pullback.fst G.hom (spMap g)) := isGrpPullback_pullback G _
  have hS' : IsSemiAbelian G' := IsSemiAbelian.pullback _ G hS
  obtain ⟨P', w, hP', hw⟩ := exists_cp_pull _ _ (spMap g) G G' _ pullback.condition (toBase_mul_pullback G _) P
  have hW' : HypW G' P'.L.L :=
    SymBaseChange.hypS_baseChange _ _ G G' _ _ _ _ P.L.isLB P'.L.isLB pb ⟨w, hw.gen⟩ hW

  let gam : FractionRing R →+* FractionRing V :=
    IsFractionRing.lift (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap V _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  have sq : spMap gam ≫ jK R = jK V ≫ spMap g :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp g _))
  obtain ⟨A', gA, pA, -, mA, tA⟩ := hL.polBaseChange _ _ (spMap gam) A
  have gpA : IsGrpPullback A'.A A.A (spMap gam) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
    have : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
    exact ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have gp' : IsGrpPullback ((Over.pullback (jK V)).obj G') G (spMap gam ≫ jK R)
      (pullback.fst G'.hom (jK V) ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback G' (jK V)).comp pb).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A'.L.pull eA.hom.left) (P'.L.L.pull (pullback.fst G'.hom (jK V))) := by
    rw [hP']
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB (pull_isLB P.L.isLB _) _)
      ((LBIso.symm tA).chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl) (Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ gen.inv.left)
      (Geo.Tor.chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => gen.hom.left) _ _ fun _ => ?_)
      (Geo.Tor.chartPullLinComb P.L.L _ _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) hA
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  obtain ⟨wA, hwA⟩ := wA
  have hpr : IsProper (pullback.snd G'.hom (jK V)) := by
    have hw : eA.hom.left ≫ A'.A.hom = pullback.snd G'.hom (jK V) := Over.w eA.hom
    have : IsIso eA.hom.left := ((Over.forget _).mapIso eA).isIso_hom
    have := A'.isAb.proper
    rw [← hw]; infer_instance

  let m := IsLocalRing.maximalIdeal V
  obtain ⟨E₀, hE₀⟩ := hsp
  let k : R ⧸ I →+* V ⧸ m ^ (0 + 1) := Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp g) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact hI ha)
  obtain ⟨E₁, -, -, -, -, hE₁⟩ := hL3.gtBaseChange _ _ (spMap k) E₀ _ hE₀
  have hc : spMap k ≫ spMap (Ideal.Quotient.mk I) = thick V m 0 ≫ spMap g :=
    (spMap_comp _ k).symm.trans (spMap_comp g (Ideal.Quotient.mk _))
  obtain ⟨e, he, -⟩ := grpPullback_iso (((isGrpPullback_pullback _ (spMap k)).comp
    (isGrpPullback_pullback G (spMap (Ideal.Quotient.mk I)))).congr hc rfl)
    ((isGrpPullback_pullback G' (thick V m 0)).comp pb)
  have := E₁.free
  have := E₁.finite
  obtain ⟨Dat⟩ := isGt_of_iso e hE₁
  obtain ⟨Q₀, -⟩ := exists_tq_of_gtDatum _ E₁ _ Dat
  obtain ⟨P₀, v, hP₀⟩ := exists_isLevelCP m 0 P'
  have hm : (m ^ (0 + 1)).IsMaximal := by rw [zero_add, pow_one]; infer_instance
  have hS₀ : IsSemiAbelian (thickObj V m 0 G') := IsSemiAbelian.pullback _ G' hS'
  have hb : Nonempty (BiTriv P₀.c Q₀.i) := by
    letI : Field (V ⧸ m ^ (0 + 1)) := Ideal.Quotient.field _
    exact @BiextTriv.main (V ⧸ m ^ (0 + 1)) _ E₁.X _ _ _ (thickObj V m 0 G') _ _ hS₀.smooth hS₀.geomConnected
      P₀.L P₀.c Q₀.i Q₀.i_hom
  obtain ⟨w₀, -, hw₀, -, -, hp, -⟩ := hW'
  have hev := EvenTriv.exists_even_cubTriv hL hL2 V G' hS' hpr P' w₀ hw₀ hp _ _ E₁.X Q₀ P₀ _ _
    (IsPullback.of_hasPullback G'.hom (thick V m 0)) v hP₀ hb
  exact ⟨A', ⟨hV, hS', eA, mE, P', wA, hwA, E₁.X, Q₀, P₀, ⟨v, hP₀⟩, hev⟩, w, hw⟩

theorem exists_unif : Laws → Laws2 → Laws3 → Ega → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → SplitOver G I → ThetaNZ G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegData R I) (U : Unif I D A G), U.LG = P.L ∧ U.gen = gen := by
  intro hL hL2 hL3 hE hU R _ _ _ I hR hpi G _ _ P hS hW hsp hθ A gen hgen hA
  have := hR.1.1
  have := hR.2.2.1
  have hI := hR.2.2.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := exists_cdvr R I
  have := hV.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : I.map φ ≤ IsLocalRing.maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨A', s, w, hw⟩ := exists_setting hL hL2 hL3 P hS hW hsp A gen hA hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  obtain ⟨D, U, rfl, rfl⟩ := GlobalTheory.T.exists_uniformization_data_complete_local_prime hL hL2 hL3 hE hU R I hR hpi G P hS hW hsp A gen hgen hA
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 hE R V I _ hR.1 hB (IsLocalRing.maximalIdeal.isMaximal V).ne_top φ hle D _ A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  obtain ⟨psi, h, Dd, hD, e, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_degData_psi_of_section_nonzero_fibres hL hL2 hE R I hR V hV φ hφ hc D D' A A' G _ U U' U₀ _ C hU' hθ
  obtain ⟨U₂, C₂, hD₂, eP, eg, k₁, k₂, k₃⟩ := exists_move psi h C hD Dd.toPre e h₁ h₂ h₃
  obtain ⟨U₁, -, hU₁, -⟩ := GlobalTheory.UnifDescent.exists_unif_of_cmp hL hL2 hE R V I _ hR.1 hB hI.ne_top φ hφ hle Dd D' A A' G _ U₂ U' U₀ _ C₂ hD₂
    hU' k₁ k₂ k₃
  exact ⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg CP.L eP), hU₁.1.symm.trans eg⟩

end GlobalTheory.PrimeUnif
end
