import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelPadicPrincipallyPolarised
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IntegralPull

section Valuation

open IsDedekindDomain Formalism.L2.Pj

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem vV_unit (u : Vˣ) : vV V (algebraMap V K' u) = 0 := by
  have : valV V (algebraMap V K' u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]

theorem vV_pos {a : V} (ha : a ≠ 0) (hu : ¬ IsUnit a) : 0 < vV V (algebraMap V K' a) := by
  have h0 : algebraMap V K' a ≠ 0 := by simpa using ha
  have : valV V (algebraMap V K' a) < 1 := by
    rw [valV, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hu
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h0) one_ne_zero).2 this
  simp only [vV]; simp at this; omega

theorem vV_irr {a : V} (ha : Irreducible a) : vV V (algebraMap V K' a) = 1 := by
  have : valV V (algebraMap V K' a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem exists_index {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (j : V →+* V') [IsLocalHom j] (i : K' →+* K'')
    (hi : ∀ v, i (algebraMap V K' v) = algebraMap V' K'' (j v)) :
    ∃ r : ℕ, 0 < r ∧ ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have inj : ∀ v, v ≠ 0 → algebraMap V' K'' (j v) ≠ 0 := fun v hv => by
    rw [← hi]; simpa using hv
  have pos : 0 < vV V' (algebraMap V' K'' (j p)) :=
    vV_pos (fun h => inj p hp.ne_zero (by simp [h])) (fun h => hp.not_isUnit (isUnit_of_map_unit j p h))
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le pos.le
  have key : ∀ v : V, v ≠ 0 → vV V' (i (algebraMap V K' v)) = (r : ℤ) * vV V (algebraMap V K' v) := by
    intro v hv
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hp
    have h1 : algebraMap V K' p ≠ 0 := by simpa using hp.ne_zero
    have h2 : algebraMap V K' u ≠ 0 := by simp
    rw [hi, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
      vV_mul (inj _ u.ne_zero) (pow_ne_zero _ (inj p hp.ne_zero)), vV_mul h2 (pow_ne_zero _ h1),
      vV_pow (inj p hp.ne_zero), vV_pow h1, vV_unit, vV_irr hp, hr]
    have := vV_unit (K' := K'') (Units.map j.toMonoidHom u)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at this
    rw [this]; ring
  refine ⟨r, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hb1 : algebraMap V K' b ≠ 0 := by simpa using hb0
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a := div_mul_cancel₀ _ hb1
  have e1 := vV_mul (V := V) hx hb1
  have e2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb1)
  rw [← map_mul, e, key a ha0, key b hb0] at e2
  rw [e] at e1
  rw [e1] at e2
  linarith

end Val

end Valuation

section Coordinates

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp JetR IsTan
open scoped CategoryTheory.Obj

section Coord

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem isUnivChart_iso {G' : Over (Spec (CommRingCat.of S))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsUnivChart G' n (fun m => x m ≫ e.inv) := by
  have one : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G') ≫ e.hom = 1 := fun T =>
    map_one (IsMonHom.monoidHom e.hom T)
  have one' : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G) ≫ e.inv = 1 := fun T => by
    rw [← one, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hm y hy => ?_⟩
  · rw [← Category.assoc, hx.1]
  · rw [← Category.assoc, hx.2.1, one']
  · have := hx.2.2 A aug m hm (y ≫ e.hom) (by rw [← Category.assoc, hy, one])
    simpa only [← Category.assoc, Iso.eq_comp_inv] using this

theorem exists_chart_of_pullback {R : Type} [CommRing R] [IsLocalRing R] {G₀ : Over (Spec (CommRingCat.of R))} [GrpObj G₀]
    [Smooth G₀.hom] (f : R →+* S) {φ : G.left ⟶ G₀.left} (h : IsGrpPullback G G₀ (Geo.Tor.spMap f) φ) :
    ∃ (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G), IsUnivChart G n x := by
  let _ := f.toAlgebra
  obtain ⟨n, x, hx⟩ := univChartLoc G₀
  obtain ⟨x', hx', -⟩ := tanBC_alg (R' := S) G₀ n x hx
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G₀ (fB R S))
  exact ⟨n, _, isUnivChart_iso e hx'⟩

variable {n : ℕ} {y : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hy : IsUnivChart G n y)
  {g : ℕ} {v : Fin g → (epsR S ⟶ G)}
include hy

theorem isTangent_of_comb (hv : ∀ i, IsTangent (v i)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) :
    IsTangent w := by
  obtain ⟨k, -⟩ := prodPts_tan hy z v fun i => (isTan_iff _).2 (hv i)
  rw [(isLieComb_iff _ _ _).1 hw]
  exact (isTan_iff _).1 k

theorem coord_inj (hv : IsLieBasis v) (tv : ∀ i, IsTan (v i)) {c c' : Fin g → S}
    (h : ∑ i, c i • tcoord hy (v i) (tv i) = ∑ i, c' i • tcoord hy (v i) (tv i)) : c = c' := by
  obtain ⟨k, e⟩ := prodPts_tan hy c v tv
  exact (hv.2 _ ((isTan_iff _).1 k)).unique ((comb_iff_coord hy c tv k).2 e)
    ((comb_iff_coord hy c' tv k).2 (e.trans h))

theorem comb_iff (hv : IsLieBasis v) {m : ℕ} {u : Fin m → (epsR S ⟶ G)} {U : Fin m → Fin g → S}
    (hU : ∀ k, IsLieComb (U k) v (u k)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) (cf : Fin m → S) :
    IsLieComb cf u w ↔ z = ∑ k, cf k • U k := by
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tu := fun k => (isTan_iff _).2 (isTangent_of_comb hy hv.1 (hU k))
  have tw := (isTan_iff _).2 (isTangent_of_comb hy hv.1 hw)
  have e : ∑ i, cf i • tcoord hy (u i) (tu i) = ∑ j, (∑ k, cf k • U k) j • tcoord hy (v j) (tv j) := by
    simp only [(comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_comm
  rw [comb_iff_coord hy cf tu tw, e, (comb_iff_coord hy z tv tw).1 hw]
  exact ⟨fun q => coord_inj hy hv tv q, fun q => by rw [q]⟩

theorem tcoord_comp (f : G ⟶ G) [IsMonHom f] {w : epsR S ⟶ G} (tw : IsTan w) :
    tcoord hy (w ≫ f) (isTan_comp tw f) = tmap hy f (tcoord hy w tw) :=
  tcoord_congr hy (congrArg (· ≫ f) (tcoord_spec hy w tw)) _ (isTan_comp (isTan_tvec hy _) f)

theorem eig_iff (hv : IsLieBasis v) (f : G ⟶ G) [IsMonHom f] {M : Matrix (Fin g) (Fin g) S}
    (hM : ∀ i, IsLieComb (M i) v (v i ≫ f)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) (r : S) :
    (w ≫ f).left = Geo.Tor.spMap (epsScaleR r) ≫ w.left ↔ z ᵥ* M = r • z := by
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tw := (isTan_iff _).2 (isTangent_of_comb hy hv.1 hw)
  have ew := (comb_iff_coord hy z tv tw).1 hw
  have e1 : tcoord hy (w ≫ f) (isTan_comp tw f) = ∑ j, (z ᵥ* M) j • tcoord hy (v j) (tv j) := by
    rw [tcoord_comp hy f tw, ew, map_sum]
    simp only [map_smul, ← tcoord_comp hy f, (comb_iff_coord hy _ tv (isTan_comp (tv _) f)).1 (hM _),
      Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have e2 : tcoord hy (spMap (scaleD r) ≫ w) (isTan_scale r tw) = ∑ j, (r • z) j • tcoord hy (v j) (tv j) := by
    rw [tcoord_scale hy r tw, ew, Finset.smul_sum]
    simp only [smul_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro q
    have q' : w ≫ f = spMap (scaleD r) ≫ w := Over.OverMorphism.ext q
    exact coord_inj hy hv tv (e1.symm.trans ((tcoord_congr hy q' _ _).trans e2))
  · intro q
    have q' : w ≫ f = spMap (scaleD r) ≫ w :=
      tan_ext hy (isTan_comp tw f) (isTan_scale r tw) (by rw [e1, e2, q])
    exact congrArg (fun t => t.left) q'

omit hy in

theorem exists_lift {R : Type} [CommRing R] {G₀ : Over (Spec (CommRingCat.of R))} [GrpObj G₀]
    (f : R →+* S) {φ : G.left ⟶ G₀.left} (h : IsGrpPullback G G₀ (Geo.Tor.spMap f) φ) (w : epsR R ⟶ G₀) :
    ∃ w' : epsR S ⟶ G, w'.left ≫ φ = Geo.Tor.spMap (dualMapR f) ≫ w.left := by
  have c : (Geo.Tor.spMap (dualMapR f) ≫ w.left) ≫ G₀.hom = (epsR S).hom ≫ Geo.Tor.spMap f := by
    rw [Category.assoc, Over.w w]
    exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg Geo.Tor.spMap (RingHom.ext fun r => by
      ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl])).trans (Geo.Tor.spMap_comp _ _))
  exact ⟨Over.homMk (h.1.lift _ _ c) (h.1.lift_snd _ _ c), h.1.lift_fst _ _ c⟩

end Coord

end Coordinates

section Generator

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open IsLocalRing ReciprocityTheory.ChartRestriction.G.H1

theorem generates_of_generic_line {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X X' : Scheme.{0}}
    (p : X ⟶ Sp V) [Flat p] {p' : X' ⟶ Sp (FractionRing V)} {φ : X' ⟶ X}
    (hφ : IsPullback φ p' p (spMap (algebraMap V (FractionRing V)))) {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (b : L'.Sec)
    (hb : ∀ s : L'.Sec, ∃ a : FractionRing V, ∀ i, s.f i = constFn p' _ a * b.f i)
    (θ : L.Sec) {g : X} (hg : p g = closedPoint V) (hθ : g ∈ Out.nonzeroLocus θ) (σ : L.Sec) :
    ∃! a : V, ∀ i, σ.f i = constFn p _ a * θ.f i := by
  obtain ⟨k₀, hb₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  have hk₀ : g ∈ L.U k₀ := X.basicOpen_le _ hb₀
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (X.mem_basicOpen _ _ hk₀).1 hb₀
  obtain ⟨w, gw'⟩ := hw
  have down := sec_pull_down ((isGen_iff w).1 gw') hL hL'
  obtain ⟨θ', hθ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V (FractionRing V))) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V (FractionRing V)))
  have : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.of_isPullback hφ.flip
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hφ.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f σ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f τ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn p' _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn p _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_pull (𝟙 _) φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk,
      (sec_eq_iff _ _ _ _).1 h₃ k y hk, Category.id_comp, hφ.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : L'.Sec} {a a' : FractionRing V}, (∀ k, s.f k = constFn p' _ a * t.f k) →
      (∀ k, t.f k = constFn p' _ a' * u.f k) → ∀ k, s.f k = constFn p' _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : L'.Sec} {a : FractionRing V}, a ≠ 0 → (∀ k, s.f k = constFn p' _ a * t.f k) →
      ∀ k, t.f k = constFn p' _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : L.Sec) (r : V), (∀ j, θ.f j = constFn p _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit p g hg hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀⟩ := hb θ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ θ' θ' 0 hθ' hθ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  obtain ⟨σK, hσK⟩ := down σ
  obtain ⟨a, ha⟩ : ∃ a : FractionRing V, ∀ i, σK.f i = constFn p' _ a * θ'.f i := by
    obtain ⟨a, ha⟩ := hb σK
    exact ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀)⟩
  obtain ⟨r, hr⟩ : ∃ r : V, ∀ i, σ.f i = constFn p _ r * θ.f i := by
    by_cases h : IsLocalization.IsInteger V a
    · obtain ⟨r, rfl⟩ := h
      exact ⟨r, inj σ θ σK θ' r hσK hθ' ha⟩
    · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
      obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
      obtain ⟨u, rfl⟩ := unit σ r (inj θ σ θ' σK r hθ' hσK (hr ▸ invc hne ha))
      exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
  refine ⟨r, hr, fun r' hr' => ?_⟩
  by_contra hne
  have e : cst p g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst p g (r' - r) * 0 := by
    rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
  exact un.ne_zero (cst_regular p g (sub_ne_zero.2 hne) e)

theorem resG_appTop_toΓ {V : Type} [CommRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) (U : X.Opens) (a : V) :
    resG X (le_top : U ≤ ⊤) (p.appTop.hom (toΓ V a)) = constFn p U a := rfl

theorem generates_of_nonzero_on_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  intro _ h₂ E _ _ _ H Dw l Xo _ T G t' x m₁ m₂ θ ⟨g, hg, hθ⟩ σ
  have := G.semi.smooth
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre h₂.secTwist amplePt Xo.univ m₁
  obtain ⟨w, hw, -⟩ := m₂.lin
  exact generates_of_generic_line G.G.hom m₂.cart.1 G.PP.isLB t'.PP.isLB ⟨w, hw⟩ b (fun s => (hb s).exists) θ hg hθ σ

end Generator

section Matching

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

def Comparison₂ {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} {B : Scheme.{0}} {t : SAB H B} {f : Sp V ⟶ B}
    (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t f) (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) : Prop :=
  ∃ (w1 : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso G.PP.L (t.PP.L.pull m2.φ)) (σ : LB.Sec G.PP.L),
    RigIso m1 w1 ∧ RigIso m2 w2 ∧ SecRel m1 w1 s σ ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) j k, m2.φ (r z) ∈ t.PP.L.U j → r z ∈ G.PP.L.U k →
      gs (r ≫ m2.φ) z _ (θ.f j) = (gw w2 r z j k).val * gs r z _ (σ.f k)

section Comparison₂

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} {B : Scheme.{0}} {t : SAB H B} {f : Sp V ⟶ B}
  (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t f) (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x))

theorem tie_iff : (∃ (w1 : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso G.PP.L (t.PP.L.pull m2.φ))
      (σ' : LB.Sec G.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (t.PP.L.pull m2.φ)),
      RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧
      ∀ g : G.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk x) Xo.univ.t.G).left = G.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ↔ Comparison₂ m1 m2 θ s := by
  constructor
  · rintro ⟨w1, w2, σ, s1, θ2, r1, r2, i1, i2, p, c⟩
    refine ⟨w1, w2, σ, r1, r2, fun Z r z j k hj hk => ?_, fun Z r z j k hj hk => ?_⟩
    · have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => j) ≤ toGx m1 ⁻¹ᵁ (PPx x).U (fun _ => j) :=
        fun q hq => le_toGx m1 j (mem_pull.1 hq)
      refine Eq.trans ?_ ((isoMaps_iff w1 σ s1).1 i1 Z r z j k hj hk)
      rw [c (toGx m1) (toGx_snd m1) (toGx_fst m1) (fun _ => j) le]
      exact (gs_appLE (toGx m1) _ _ le r z (mem_pull.2 hj) _).symm
    · have le : (t.PP.L.pull m2.φ).U (fun _ => j) ≤ m2.φ ⁻¹ᵁ t.PP.L.U j := fun q hq => mem_pull.1 hq
      refine Eq.trans ?_ ((isoMaps_iff w2 σ θ2).1 i2 Z r z j k hj hk)
      rw [p (fun _ => j) le]
      exact (gs_appLE m2.φ _ _ le r z (mem_pull.2 hj) _).symm
  · rintro ⟨w1, w2, σ, r1, r2, a, b⟩
    obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w1).1 r1.1) Xo.univ.t.PP.isLB G.PP.isLB σ
    refine ⟨w1, w2, σ, s1, thfPull t.PP.L m2.φ θ, r1, r2,
      (isoMaps_iff w1 σ s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk,
      (isoMaps_iff w2 σ _).2 fun Z r z j k hj hk =>
        (gs_appLE m2.φ _ _ _ r z (mem_pull.2 hj) _).trans (b Z r z j k hj hk), fun _ _ => rfl, ?_⟩
    intro g e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    have eg : g = toGx m1 := by
      apply FramedBaseChange.pulledGroup_hom_ext
      · rw [e₁, toGx_snd]
      · rw [e₂, toGx_fst]
    subst eg
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart G.PP.isLB p
    rw [hs1 _ (𝟙 _) p J k hp hk, gs_appLE _ _ _ hJ (𝟙 _) p hp, a _ (𝟙 _) p _ k (mem_pull.1 hp) hk]

theorem tie_pull {V' : Type} [CommRing V'] {x' : Sp V' ⟶ Xo.X} {G' : SAB H (Sp V')} {f' : Sp V' ⟶ B}
    {g : Sp V' ⟶ Sp V} (n : SABMap G' G g) (m1' : SABMap G' Xo.univ.t x') (m2' : SABMap G' t f')
    (hx : x' = g ≫ x) (hf : f' = g ≫ f) (e₁ : m1'.φ = n.φ ≫ m1.φ) (e₂ : m2'.φ = n.φ ≫ m2.φ)
    (s' : LB.Sec (PPx x')) (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (hb : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ g)
    (ha : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x') (z : Z) (j : Xo.univ.t.PP.L.ι), r z ∈ (PPx x').U (fun _ => j) →
      gs r z _ (s'.f (fun _ => j)) = gs (r ≫ pm) z _ (s.f (fun _ => j)))
    (h : Comparison₂ m1 m2 θ s) : Comparison₂ m1' m2' θ s' := by
  obtain ⟨w1, w2, σ, r1, r2, a, b⟩ := h
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨w1', r1', T1⟩ := cube_rig_comp m1.cm n.cm m1'.cm e₁ (by rw [m1'.base, n.base, m1.base, hx]) _ _ _ w1 w0 r1 r0
  obtain ⟨w2', r2', T2⟩ := cube_rig_comp m2.cm n.cm m2'.cm e₂ (by rw [m2'.base, n.base, m2.base, hf]) _ _ _ w2 w0 r2 r0
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 r0.1) G.PP.isLB G'.PP.isLB σ
  refine ⟨w1', w2', σ', r1', r2', fun Z r z j k hj hk => ?_, fun Z r z j k hj hk => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart G.PP.isLB (n.φ (r z))
    have hm : m1.φ ((r ≫ n.φ) z) ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (fun q => q (r z) ∈ Xo.univ.t.PP.L.U j) e₁).mp hj
    have eg : (r ≫ toGx m1') ≫ pm = (r ≫ n.φ) ≫ toGx m1 := by
      rw [Category.assoc, Category.assoc]
      congr 1
      apply FramedBaseChange.pulledGroup_hom_ext
      · rw [Category.assoc, hs, toGx_snd, e₁, Category.assoc, toGx_snd]
      · rw [Category.assoc, hb, ← Category.assoc, toGx_fst, Category.assoc, toGx_fst]
        exact n.cart.1.w.symm
    rw [ha Z (r ≫ toGx m1') z j (le_toGx m1' j hj), eg, a Z (r ≫ n.φ) z j i hm hi, hσ' Z r z i k hi hk,
      T1 Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc]
  · obtain ⟨i, hi⟩ := exists_chart G.PP.isLB (n.φ (r z))
    have hm : m2.φ ((r ≫ n.φ) z) ∈ t.PP.L.U j :=
      (congrArg (fun q => q (r z) ∈ t.PP.L.U j) e₂).mp hj
    have eg : r ≫ m2'.φ = (r ≫ n.φ) ≫ m2.φ := by rw [e₂, Category.assoc]
    refine (congrArg (fun q => gs q z _ (θ.f j)) eg).trans ?_
    rw [b Z (r ≫ n.φ) z j i hm hi, hσ' Z r z i k hi hk,
      T2 Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc]

end Comparison₂

end Matching

section Cancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

theorem flat_of_injective {A V : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing V] [IsDomain V]
    (f : A →+* V) (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul A V := (faithfulSMul_iff_algebraMap_injective A V).2 hf
  show Module.Flat A V
  infer_instance

theorem isTan_iff_isTangent {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {G : SAB H S'} {t' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (m : SABMap G t f) (n : SABMap t' G g) (k : SABMap t' t h) (hb : h = g ≫ f)
    (hφ : k.φ = n.φ ≫ m.φ) (θ : LB.Sec t.PP.L) (w : LB.Iso t'.PP.L (t.PP.L.pull k.φ)) (σ : LB.Sec t'.PP.L)
    (θ2 : LB.Sec (t.PP.L.pull k.φ)) (r : RigIso k w) (hi : IsoMaps w σ θ2) (hp : PullSec k.φ θ θ2) :
    ∃ (θ' : LB.Sec G.PP.L) (w' : LB.Iso t'.PP.L (G.PP.L.pull n.φ)),
      (∀ s : S', (∃ x : t.G.left, t.G.hom x = f s ∧ x ∈ Out.nonzeroLocus θ) →
        ∃ x : G.G.left, G.G.hom x = s ∧ x ∈ Out.nonzeroLocus θ') ∧
      RigIso n w' ∧ IsoMaps w' σ (thfPull G.PP.L n.φ θ') := by
  obtain ⟨w0, g0, r0, -⟩ := m.lin
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) t.PP.isLB G.PP.isLB θ
  have he : k.cm.e = n.cm.e ≫ m.cm.e := by rw [k.base, n.base, m.base, hb]
  obtain ⟨w', r', tri⟩ := GlobalTheory.Reg.TieIntegral.exists_rigIso_cancel m.cm n.cm k.cm hφ he t'.PP G.PP t.PP w0 w ⟨g0, r0⟩ r
  refine ⟨θ', w', ?_, r', fun (i : PUnit → G.PP.L.ι) k' => fn_ext fun y hy => ?_⟩
  · rintro s ⟨z, hz, hz'⟩
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z s hz
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨i, hi⟩ := exists_chart G.PP.isLB y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨i, hi, ?_⟩⟩
    have u₁ : IsUnit (gs m.φ y _ (θ.f j)) := by rw [gs_stalkMap m.φ y _ hj]; exact u.map _
    have e := hθ' _ (𝟙 _) y j i hj hi
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · have hi' : n.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
    obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (n.φ y))
    have pt : k.φ y = m.φ (n.φ y) := congrArg (fun q => q y) hφ
    have hj' : k.φ y ∈ t.PP.L.U j := pt ▸ hj
    have e1 := hθ' _ (𝟙 _ ≫ n.φ) y j (i PUnit.unit) hj hi'
    have e2 : gs (𝟙 _ ≫ k.φ) y _ (θ.f j) = (gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ.f k') := by
      have hz : y ∈ (t.PP.L.pull k.φ).U (fun _ => j) ⊓ t'.PP.L.U k' := ⟨mem_pull.2 hj', hy.2⟩
      have le : (t.PP.L.pull k.φ).U (fun _ => j) ≤ k.φ ⁻¹ᵁ t.PP.L.U j := fun q hq => mem_pull.1 hq
      have a := congrArg (gs (𝟙 _) y _) (hi (fun _ => j) k')
      refine (gs_appLE k.φ _ _ le (𝟙 _) y hz.1 _).symm.trans ?_
      rw [← hp (fun _ => j) le]
      exact (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have e3 := tri _ (𝟙 _) y j (i PUnit.unit) k' hj hi' hy.2
    have e4 : (𝟙 _ ≫ n.φ) ≫ m.φ = 𝟙 _ ≫ k.φ := by rw [Category.assoc, hφ]
    rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
    refine (gs_res _ y _ hy _).trans ((gs_appLE n.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

end Cancel

section Lie

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Matrix

theorem eigenbasis_baseChange {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {V S : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing S] (f : V →+* S) (hflat : f.Flat)
    (G : SAB H (Sp V)) (G' : SAB H (Sp S)) (m : SABMap G' G (spMap f)) (ρ : 𝓞 E → V) {n : ℕ}
    (v₀ : Fin n → (epsR V ⟶ G.G)) (h₁ : ∀ k, IsTangent (v₀ k))
    (h₂ : ∀ k x, (v₀ k ≫ G.act.act x).left = spMap (epsScaleR (ρ x)) ≫ (v₀ k).left)
    (h₃ : ∀ w : epsR V ⟶ G.G, IsTangent w → (∀ x, (w ≫ G.act.act x).left = spMap (epsScaleR (ρ x)) ≫ w.left) →
      ∃! cf : Fin n → V, IsLieComb cf v₀ w) :
    ∃ u : Fin n → (epsR S ⟶ G'.G), (∀ k, (u k).left ≫ m.φ = spMap (dualMap f) ≫ (v₀ k).left) ∧
      (∀ k, IsTangent (u k)) ∧
      (∀ k x, (u k ≫ G'.act.act x).left = spMap (epsScaleR (f (ρ x))) ≫ (u k).left) ∧
      ∀ w : epsR S ⟶ G'.G, IsTangent w →
        (∀ x, (w ≫ G'.act.act x).left = spMap (epsScaleR (f (ρ x))) ≫ w.left) →
        ∃! cf : Fin n → S, IsLieComb cf u w := by
  have hsm : Smooth G.G.hom := G.semi.smooth
  have hmon : ∀ x, IsMonHom (G.act.act x) := G.act.hom
  have hmon' : ∀ x, IsMonHom (G'.act.act x) := G'.act.hom
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis G.G hsm
  obtain ⟨d, y, hy⟩ := Chart.univChartLoc G.G
  obtain ⟨d', y', hy'⟩ := exists_chart_of_pullback f m.cart
  choose U hU using fun k => (hv.2 _ (h₁ k)).exists
  choose M hM using fun x i => (hv.2 (v i ≫ G.act.act x)
    ((Chart.isTan_iff _).1 (Chart.isTan_comp ((Chart.isTan_iff _).2 (hv.1 i)) _))).exists
  choose u hu using fun k => exists_lift f m.cart (v₀ k)
  choose v' hv' using fun j => exists_lift f m.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange f m.cart hv hv'
  have hU' : ∀ k, IsLieComb (fun j => f (U k j)) v' (u k) := fun k =>
    Chart.comb_baseChange f m.cart (hU k) hv' (hu k)
  have hMR : ∀ x i, IsLieComb (Matrix.of (M x) i) v (v i ≫ G.act.act x) := hM
  have hM' : ∀ x i, IsLieComb ((Matrix.of (M x)).map f i) v' (v' i ≫ G'.act.act x) := fun x i =>
    Chart.comb_baseChange f m.cart (hM x i) hv' (by
      rw [Over.comp_left, Category.assoc, m.act, ← Category.assoc, hv', Category.assoc, Over.comp_left])
  have hUe : ∀ k x, U k ᵥ* Matrix.of (M x) = ρ x • U k := fun k x =>
    (eig_iff hy hv _ (hMR x) (hU k) _).1 (h₂ k x)
  refine ⟨u, hu, fun k => isTangent_of_comb hy' hb'.1 (hU' k), fun k x => ?_, fun w hw hwe => ?_⟩
  · refine (eig_iff hy' hb' _ (hM' x) (hU' k) _).2 ?_
    funext j
    have := congrArg f (congrFun (hUe k x) j)
    simpa [Matrix.vecMul, dotProduct] using this
  · obtain ⟨z, hz, -⟩ := hb'.2 w hw
    simp only [comb_iff hy' hb' hU' hz]
    let _ := f.toAlgebra
    have : Module.Flat V S := hflat
    refine (GlobalTheory.commonEigenvectors_flat_baseChange V (𝓞 E) g n (fun x => Matrix.of (M x)) ρ).1 V U hUe
      (fun s hs => ?_) S z (fun x => (eig_iff hy' hb' _ (hM' x) hz _).1 (hwe x))
    simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hs ⊢
    have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := h₃ _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv hU hc] using this

end Lie

section Int

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_eigenvalue (T : CDVR) (io : c.F →+* T.Fr) (τ : E →+* ℂ) (a : 𝓞 E) :
    ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ a) := by
  have h : IsIntegral T.V ((io.comp (embK c τ)) a) :=
    (RingOfIntegers.isIntegral a).map_of_comp_eq (algebraMap ℤ T.V) _ (RingHom.ext_int _ _)
  exact IsIntegrallyClosed.isIntegral_iff.1 h

theorem exists_nonzero_of_generator (T : CDVR) (G : SAB H (Sp T.V)) (t : SAB H (Sp T.Fr)) {x : Sp T.Fr ⟶ Xo.X}
    (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L)
    (hθ : ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
      σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) (s : Sp T.V) :
    ∃ g : G.G.left, G.G.hom g = s ∧ g ∈ nonzeroLocus θ := by
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws
  have hprop : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G G t hprop m2 m2
  have hp := GlobalTheory.UnifAfterExt.polAt_of_sabMap ψ m2 m1 Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK T.V) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨σ, hσ⟩ := GlobalTheory.ThetaDvr.thetaNZ_of_polAt L₁ L₂ E H T.V G hp
  obtain ⟨g, i, hg, hi⟩ := hσ s
  obtain ⟨a, ha, -⟩ := hθ σ
  rw [ha i, Scheme.basicOpen_mul] at hi
  exact ⟨g, hg, TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi.2⟩⟩

theorem integral_baseChange (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (f : T.V →+* T'.V)
    (hf : Function.Injective f) :
    letI := io.toAlgebra
    letI := io'.toAlgebra
    ∀ (ψ : T.Fr →ₐ[c.F] T'.Fr), (∀ a, ψ (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (f a)) →
      ∀ (y : FrPt Xo c T.Fr) (y' : FrPt Xo c T'.Fr), FrMap ψ y y' → Integral T io y → Integral T' io' y' := by
  letI := io.toAlgebra
  letI := io'.toAlgebra
  intro ψ hψ y y' hm hy
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨G, t, m1, m2, ⟨ub, h₁, h₂, h₃, h₄⟩, θ, hθ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩ := hy
  obtain ⟨hx, hu, pm, hs, hb, ha⟩ := hm
  obtain ⟨G', ⟨m⟩⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap f)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', ⟨n⟩⟩ : ∃ t' : SAB H (Sp T'.Fr), Nonempty (SABMap t' t (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) t
    exact ⟨_, ⟨m⟩⟩
  have hι : ψ.toRingHom.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp f := RingHom.ext hψ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap f = spMap ψ.toRingHom ≫ spMap (algebraMap T.V T.Fr) := by
    rw [← sp_comp, ← sp_comp, hι]
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨m1', e₁, -⟩ := exists_comp_rig m1 n y'.x hx a1 r0
  obtain ⟨m2', e₂, -⟩ := exists_comp_rig m2 n _ hio a2 r0
  have T₀ := (tie_iff m1 m2 θ y.s).1 ⟨w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩
  have T₁ := tie_pull m1 m2 θ y.s n m1' m2' hx hio e₁ e₂ y'.s pm hs hb (fun Z r z j hz => by
    have hle := FramedBaseChange.chart_le pm hs (fun _ => j)
    rw [← ha _ hle, gs_appLE pm _ _ hle r z hz]) T₀
  obtain ⟨w1', w2', σ', s1', θ2', r1, r2, i1, i2, p2, hg⟩ := (tie_iff m1' m2' θ y'.s).2 T₁
  obtain ⟨m', e₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m m2'
  obtain ⟨θ', w', hnz, r', i'⟩ := sec_cancel m m' m2' rfl e₃ θ w2' σ' θ2' r2 i2 p2
  choose ρ hρ using exists_eigenvalue (c := c) T io
  have eig : ∀ (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (τ : E →+* ℂ) (ρ : 𝓞 E → T.V),
      (∀ x, algebraMap T.V T.Fr (ρ x) = io (embK c τ x)) → ∀ w : epsR T.V ⟶ G.G,
      IsEigV c io G τ w ↔ ∀ x : 𝓞 E, (w ≫ G.act.act x).left = spMap (epsScaleR (ρ x)) ≫ w.left :=
    fun T io G τ ρ hρ w => ⟨fun h x => h x _ (hρ x), fun h x s hs => by
      obtain rfl : s = ρ x := IsFractionRing.injective T.V T.Fr (hs.trans (hρ x).symm)
      exact h x⟩
  have hρ' : ∀ τ x, algebraMap T'.V T'.Fr (f (ρ τ x)) = io' (embK c τ x) := fun τ x => by
    rw [← hψ, hρ]
    exact ψ.commutes _
  choose u k₁ k₂ k₃ k₄ using fun τ => eigenbasis_baseChange f (flat_of_injective f hf) G G' m (ρ τ) (ub τ)
    (fun k => (isTan_iff_isTangent _).1 (h₁ τ k)) (fun k => (eig T io G τ _ (hρ τ) _).1 (h₂ τ k))
    (fun w hw he => h₃ τ w ((isTan_iff_isTangent _).2 hw) ((eig T io G τ _ (hρ τ) _).2 he))
  refine ⟨G', t', m1', m', ⟨u, fun τ i => (isTan_iff_isTangent _).2 (k₂ τ i), fun τ i => (eig T' io' G' τ _ (hρ' τ) _).2 (k₃ τ i),
    fun τ w h1 h2 => k₄ τ w ((isTan_iff_isTangent _).1 h1) ((eig T' io' G' τ _ (hρ' τ) w).1 h2), fun τ i => ?_⟩, θ',
    generates_of_nonzero_on_special_fibre L₁ L₂ E H Dw l Xo c T' G' t' y'.x m1' m' θ'
      (hnz _ (exists_nonzero_of_generator T G t m1 m2 θ hθ _)),
    w1', w', σ', s1', thfPull G'.PP.L m'.φ θ', r1, r', i1, i', fun _ _ => rfl, hg⟩
  obtain ⟨q, q1, q2⟩ := h₄ τ i
  have ub₀ : (ub τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ i)
  have ub₁ : (u τ i).left ≫ G'.G.hom = spMap (algebraMap T'.V (DualNumber T'.V)) := Over.w (u τ i)
  have hpre : IsPreimmersion (spMap (algebraMap T.V T.Fr)) := IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
  have qb : q ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, q2,
      Category.assoc, ub₀, dual_alg]
  have cnd : (spMap (dualMap ψ.toRingHom) ≫ q) ≫ t.G.hom =
      spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap ψ.toRingHom := by
    rw [Category.assoc, qb, dual_alg]
  have p1 := n.cart.1.lift_fst _ _ cnd
  have p2 := n.cart.1.lift_snd _ _ cnd
  refine ⟨n.cart.1.lift _ _ cnd, ?_, ?_⟩
  · rw [e₁, ← Category.assoc, p1, Category.assoc, q1, hu]
  · apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, k₁, ← e₃, e₂, ← Category.assoc, p1, Category.assoc, q2, ← Category.assoc,
        ← Category.assoc, ← dual_comp, ← dual_comp, hι]
    · rw [Category.assoc, Category.assoc, m'.cart.1.w, ← Category.assoc, p2, ub₁, dual_alg]

theorem exists_unif_of_split (T T' : CDVR) (f : T.V →+* T'.V) (ψ : T.Fr →+* T'.Fr)
    (hψ : ∀ a, ψ (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (f a))
    {G : SAB H (Sp T.V)} {t : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} (m1 : SABMap t Xo.univ.t x)
    (m2 : SABMap t G (spMap (algebraMap T.V T.Fr))) {G' : SAB H (Sp T'.V)} {t' : SAB H (Sp T'.Fr)}
    {x' : Sp T'.Fr ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) (m1' : SABMap t' Xo.univ.t x')
    (m2' : SABMap t' G' (spMap (algebraMap T'.V T'.Fr)))
    (hS : ∃ S : SplitExt (Sp (ResidueField T'.V)), S.IsGt ((Over.pullback (spMap (residue T'.V))).obj
      ((Over.pullback (spMap f)).obj G.G))) :
    ∃ P : PELUnif (maximalIdeal T'.V) G', P.TorsionIso := by
  subst hx
  have hι : ψ.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp f := RingHom.ext hψ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap f = spMap ψ ≫ spMap (algebraMap T.V T.Fr) := by
    rw [← sp_comp, ← sp_comp, hι]
  obtain ⟨tP, ⟨mP⟩⟩ : ∃ tP : SAB H (Sp T'.V), Nonempty (SABMap tP G (spMap f)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨n, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m1 m1'
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨w2, r2⟩ := exists_rigIso m2
  obtain ⟨k, -, -⟩ := exists_comp_rig m2 n _ hio r2 r0
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mP k
  have hprop : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1'.cart.1 Xo.univ.proper
  obtain ⟨j, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T'.V inferInstance G' tP t' hprop m2' mK
  have hp := GlobalTheory.UnifAfterExt.polAt_of_sabMap j mK m1' Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK T'.V) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨S, hS⟩ := hS
  obtain ⟨e, he, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback _ (spMap (residue T'.V))).comp (isGrpPullback_pullback G.G (spMap f)))
    ((isGrpPullback_pullback _ (spMap (residue T'.V))).comp ((j.cart.comp mP.cart).congr (Category.id_comp _) rfl))
  obtain ⟨-, P, -, hP⟩ := GlobalTheory.UnifAfterExt.isOpen_and_uniformised T'.V inferInstance G' hp ⟨S, isGt_of_iso e hS⟩
  exact ⟨P, hP⟩

end Int

end GlobalTheory.IntegralPull
