import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry
open GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.TrueGeo.InducedPull

namespace GlobalTheory.ShFam.GalCarry

section IsoTransport

variable {F : Type} [Field F] [NumberField F] {Y Y' : Var F}

def modelOfIso (M' : Model Y') (φ : Y.X ≅ Y'.X) (hs : φ.hom ≫ Y'.str = Y.str) (hd : Y.dim = Y'.dim) :
    Model Y where
  X := M'.X
  p := M'.p
  ar := hd ▸ M'.ar
  j := φ.hom ≫ M'.j
  pb := by
    have H : IsPullback φ.hom Y.str Y'.str (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hs, Category.comp_id]⟩
    simpa using H.paste_horiz M'.pb

omit [NumberField F] in

theorem valAt_mul' {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {a b : Z.functionField}
    (ha : RegAt (below y) a) (hb : RegAt (below y) b) : valAt y (a * b) = valAt y a * valAt y b := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨z', rfl⟩ := hb
  rw [← map_mul, Base.valAt_stalk, Base.valAt_stalk, Base.valAt_stalk, map_mul]

theorem mem_pull_comp {T T' Z : Scheme.{0}} (B : LB Z) (f : T ⟶ T') (j : T' ⟶ Z) (i : (B.pull j).ι) (x : T) :
    x ∈ (B.pull (f ≫ j)).U i ↔ f x ∈ (B.pull j).U i :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k,
    fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k⟩

omit [NumberField F] in

theorem map_fnOf {f : Y.X ⟶ Y'.X} {ψ : Y'.Fn →+* Y.Fn} (hg : genericPt Y ≫ f = spMap ψ ≫ genericPt Y')
    {U' : Y'.X.Opens} {U : Y.X.Opens} (l : U ≤ f ⁻¹ᵁ U') (h : genericPoint Y.X ∈ U)
    (h' : genericPoint Y'.X ∈ U') (a : Γ(Y'.X, U')) :
    ψ (fnOf U' h' a) = fnOf U h ((f.appLE U' U l).hom a) := by
  rw [← algebraMap_germ (U := U') (x := f (genericPoint Y.X)) (l h) a, ← algebraMap_germ h, map_alg hg]
  congr 1
  refine (Scheme.Hom.germ_stalkMap_apply f U' (genericPoint Y.X) (l h) a).trans ?_
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

omit [NumberField F] in

theorem isRatSec_pull_comp {Z : Scheme.{0}} (B : LB Z) (j : Y'.X ⟶ Z) {f : Y.X ⟶ Y'.X} {ψ : Y'.Fn →+* Y.Fn}
    (hg : genericPt Y ≫ f = spMap ψ ≫ genericPt Y') {r' : (B.pull j).ι → Y'.Fnˣ}
    (hr : IsRatSec (B.pull j) r') (c : Y.Fnˣ) :
    IsRatSec (B.pull (f ≫ j)) fun i => Units.map (ψ : Y'.Fn →* Y.Fn) (r' i) * c := by
  intro i i' h
  have l : (B.pull (f ≫ j)).U i ⊓ (B.pull (f ≫ j)).U i' ≤ f ⁻¹ᵁ ((B.pull j).U i ⊓ (B.pull j).U i') :=
    fun _ hx => ⟨(mem_pull_comp B f j i _).1 hx.1, (mem_pull_comp B f j i' _).1 hx.2⟩
  have h' : genericPoint Y'.X ∈ (B.pull j).U i ⊓ (B.pull j).U i' :=
    gen_mem (X := Y'.X) (U := (B.pull j).U i ⊓ (B.pull j).U i') (x := f (genericPoint Y.X)) (l h)
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  rw [hr i i' h', map_mul, map_fnOf hg l h h', mul_assoc]
  congr 2
  rw [val_pull_g B j i i' (inf_le B j i i'), val_pull_g B (f ≫ j) i i' (inf_le B (f ≫ j) i i')]
  have e := Scheme.Hom.appLE_comp_appLE f j _ _ _ (inf_le B j i i') l
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) _

omit [NumberField F] in

theorem presents_pull_comp {Z : Scheme.{0}} {B : LB Z} (hB : B.IsLB) (j : Y'.X ⟶ Z) {D : Y.Dv}
    {D' : Y'.Dv} {φ : Y.X ≅ Y'.X} {ψ : Y'.Fn →+* Y.Fn} {u : Y.Fnˣ} (h : DivIso D D' φ ψ u) (k : ℕ)
    {r' : (B.pull j).ι → Y'.Fnˣ} (hr : Presents (k • D') (B.pull j) r') :
    Presents (k • D) (B.pull (φ.hom ≫ j)) fun i => Units.map (ψ : Y'.Fn →* Y.Fn) (r' i) * u ^ k := by
  refine ⟨LB.isLB_pull hB _, isRatSec_pull_comp B j h.2.1 hr.isRatSec _, fun i x hx => ?_⟩
  have hg := Base.isEqn_eqn D' (φ.hom x)
  have e' := (hg.nsmul k).iff_unitAt.1 (hr.isEqn i (φ.hom x) ((mem_pull_comp B φ.hom j i x).1 hx))
  refine ((h.2.2.2 x _ hg).nsmul k).iff_unitAt.2 ?_
  have := unitAt_map h.2.1 e'
  convert this using 1
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, map_div₀, map_pow, mul_pow]
  exact mul_div_mul_right _ _ (pow_ne_zero _ u.ne_zero)

omit [NumberField F] in

theorem ratVal_map {f : Y.X ⟶ Y'.X} {ψ : Y'.Fn →+* Y.Fn} (hg : genericPt Y ≫ f = spMap ψ ≫ genericPt Y')
    (hs : f ≫ Y'.str = Y.str) {σ : F →+* ℂ} (y : Pts Y σ) (y' : Pts Y' σ) (hy : y'.1 = y.1 ≫ f)
    {a : Y'.Fn} (ha : RegAt (under y') a) : ratVal (ψ a) y = ratVal a y' := by
  obtain ⟨U', hU', b, rfl⟩ := ha.exists_fnOf
  have hx : under y ∈ f ⁻¹ᵁ U' := by
    have e : under y' = f (under y) := by
      show y'.1 _ = f (y.1 _)
      rw [hy]
      rfl
    show f (under y) ∈ U'
    exact e ▸ hU'
  have hy' : y' ∈ ptsIn Y'.str σ U' := mem_ptsIn.2 hU'
  rw [map_fnOf hg le_rfl (gen_mem hx), ratVal_fnOf (mem_ptsIn.2 hx), ratVal_fnOf hy', ← Scheme.Hom.app_eq_appLE,
    ev_app f hs]
  congr 1
  exact Subtype.ext hy.symm

variable {C : CxSt F}

theorem induced_of_adlIso {A : Adl C Y} {A' : Adl C Y'} {φ : Y.X ≅ Y'.X} {ψ : Y'.Fn →+* Y.Fn} {u : Y.Fnˣ}
    (h : AdlIso A A' φ ψ u) {M' : Model Y'} {L : HermLB M'.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 F) → ℝ}
    (hI : A'.Induced M' L k cf) : A.Induced (modelOfIso M' φ h.1.1 h.1.2.2.1) L k cf := by
  obtain ⟨⟨hs, hg, hd, hD⟩, hn, hci, harch, hfin⟩ := h
  obtain ⟨h₀, r', hr, h₁, h₂⟩ := hI
  refine ⟨h₀, fun i => Units.map (ψ : Y'.Fn →* Y.Fn) (r' i) * u ^ (k : ℕ),
    presents_pull_comp L.isLB M'.j ⟨hs, hg, hd, hD⟩ k hr, ?_, ?_⟩
  · intro σ y y' i f hy hi hf
    let y₂ : Pts Y' σ := ⟨y.1 ≫ φ.hom, by rw [Category.assoc, hs, y.2]⟩
    have hi' : under y₂ ∈ (L.B.pull M'.j).U i := (mem_pull_comp L.B φ.hom M'.j i _).1 hi
    have hy' : y'.1 = y₂.1 ≫ M'.j := hy.trans (Category.assoc _ _ _).symm
    obtain ⟨g, hg'⟩ : ∃ g, A'.D.IsEqn (under y₂) g := ⟨_, Base.isEqn_eqn _ _⟩
    have hG : A.D.IsEqn (under y) (Units.map (ψ : Y'.Fn →* Y.Fn) g * u) := hD _ g hg'
    have hk := hG.nsmul (k : ℕ)
    have hk' := hg'.nsmul (k : ℕ)
    have ha := hk.regularAt_iff.1 hf
    have hreg : ((k : ℕ) • A.D).RegularAt (under y)
        (((Units.map (ψ : Y'.Fn →* Y.Fn) g * u : Y.Fnˣ) : Y.Fn)⁻¹ ^ (k : ℕ)) := by
      refine hk.regularAt_iff.2 ?_
      rw [Units.val_pow_eq_pow_val, ← mul_pow, inv_mul_cancel₀ (Units.ne_zero _), one_pow]
      exact (unitAt_one _).regAt
    have hreg' : ((k : ℕ) • A'.D).RegularAt (under y₂) ((g : Y'.Fn)⁻¹ ^ (k : ℕ)) := by
      refine hk'.regularAt_iff.2 ?_
      rw [Units.val_pow_eq_pow_val, ← mul_pow, inv_mul_cancel₀ (Units.ne_zero _), one_pow]
      exact (unitAt_one _).regAt
    have hb : UnitAt (under y₂) ((g : Y'.Fn)⁻¹ ^ (k : ℕ) * (r' i : Y'.Fn)) := by
      have := hk'.iff_unitAt.1 (hr.isEqn i _ hi')
      rwa [Units.val_pow_eq_pow_val, div_eq_mul_inv, mul_comm, ← inv_pow] at this
    have e1 := harch σ y y₂ rfl g hg'
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val] at e1
    have e2 := h₁ σ y₂ y' i _ hy' hi' hreg'
    rw [← hn, ← hci] at e2
    have e3 := C.pn_mPow Y σ A.D k (A.m σ) _ y (CartierDiv.isEqn_iff_generatesAt_inv.1 hG)
    have e4 := C.pn_mPow Y' σ A'.D k (A'.m σ) _ y₂ (CartierDiv.isEqn_iff_generatesAt_inv.1 hg')
    have e5 := C.pn_mul Y σ _ (C.mPow Y σ A.D k (A.m σ)) _ _ y ha hreg
    have e6 := ratVal_mul ha (unitAt_map hg hb).regAt
    have e7 := ratVal_map hg hs y y₂ rfl hb.regAt
    have hf_eq : f = f * ((Units.map (ψ : Y'.Fn →* Y.Fn) g * u) ^ (k : ℕ) : Y.Fnˣ) *
        ((Units.map (ψ : Y'.Fn →* Y.Fn) g * u : Y.Fnˣ) : Y.Fn)⁻¹ ^ (k : ℕ) := by
      rw [Units.val_pow_eq_pow_val, mul_assoc, ← mul_pow, mul_inv_cancel₀ (Units.ne_zero _), one_pow, mul_one]
    have hr_eq : f * ((Units.map (ψ : Y'.Fn →* Y.Fn) (r' i) * u ^ (k : ℕ) : Y.Fnˣ) : Y.Fn) =
        f * ((Units.map (ψ : Y'.Fn →* Y.Fn) g * u) ^ (k : ℕ) : Y.Fnˣ) *
          ψ ((g : Y'.Fn)⁻¹ ^ (k : ℕ) * (r' i : Y'.Fn)) := by
      have hψ : ψ (g : Y'.Fn) ≠ 0 := (Units.map (ψ : Y'.Fn →* Y.Fn) g).ne_zero
      have hh : ψ (g : Y'.Fn) ^ (k : ℕ) * (ψ (g : Y'.Fn))⁻¹ ^ (k : ℕ) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hψ, one_pow]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, map_mul, map_pow,
        map_inv₀, mul_pow]
      linear_combination (-(f * ψ (r' i : Y'.Fn) * (u : Y.Fn) ^ (k : ℕ))) * hh
    conv_lhs => rw [hf_eq]
    rw [e4] at e2
    rw [e5, e3, e1, hr_eq, e6, e7, norm_mul, mul_pow, mul_left_comm, e2]
    ring
  · intro v e y yt i hy hi
    let y₂ : AlgPt Y' := ⟨y.1 ≫ φ.hom, by rw [Category.assoc, hs, y.2]⟩
    have e2 := h₂ v e y₂ yt i (hy.trans (Category.assoc _ _ _).symm) hi
    have e1 := hfin v e y y₂ rfl
    rw [← hn] at e2
    have hg' := Base.isEqn_eqn A'.D (below y₂.1)
    have hgA := Base.isEqn_eqn A.D (below y.1)
    have hc : UnitAt (below y.1) (((Units.map (ψ : Y'.Fn →* Y.Fn) (eqn A'.D (below y₂.1)) * u *
        (eqn A.D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn)) := by
      have := hgA.iff_unitAt.1 (hD _ _ hg')
      rwa [Units.val_mul _ (eqn A.D (below y.1))⁻¹, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
    have hmem : below y₂.1 ∈ (L.B.pull M'.j).U i := by
      refine Set.mem_iInter.2 fun _ => ?_
      have hy2 : spMap e.O.subtype ≫ yt = y₂.1 ≫ M'.j := hy.trans (Category.assoc _ _ _).symm
      have h3 : (y₂.1 ≫ M'.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit) := by
        rw [← hy2]
        exact hi (show (spMap e.O.subtype) (IsLocalRing.closedPoint _) ∈ (⊤ : Scheme.Opens _) from trivial)
      exact h3
    have hb : UnitAt (below y₂.1) (((eqn A'.D (below y₂.1))⁻¹ ^ (k : ℕ) * r' i : Y'.Fnˣ) : Y'.Fn) := by
      have := (hg'.nsmul (k : ℕ)).iff_unitAt.1 (hr.isEqn i _ hmem)
      rwa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow, inv_mul_eq_div,
        ← Units.val_pow_eq_pow_val]
    have hcr : RegAt (below y.1) ((((Units.map (ψ : Y'.Fn →* Y.Fn) (eqn A'.D (below y₂.1)) * u *
        (eqn A.D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn)) ^ (k : ℕ)) := by
      obtain ⟨z, -, hz⟩ := hc
      exact ⟨z ^ (k : ℕ), by rw [map_pow, hz]⟩
    have key : (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * (Units.map (ψ : Y'.Fn →* Y.Fn) (r' i) * u ^ (k : ℕ)) :
        Y.Fnˣ) : Y.Fn) = ψ (((eqn A'.D (below y₂.1))⁻¹ ^ (k : ℕ) * r' i : Y'.Fnˣ) : Y'.Fn) *
          (((Units.map (ψ : Y'.Fn →* Y.Fn) (eqn A'.D (below y₂.1)) * u * (eqn A.D (below y.1))⁻¹ : Y.Fnˣ) :
            Y.Fn)) ^ (k : ℕ) := by
      have hψ : ψ (eqn A'.D (below y₂.1) : Y'.Fn) ≠ 0 := (Units.map (ψ : Y'.Fn →* Y.Fn) _).ne_zero
      have hh : ψ (eqn A'.D (below y₂.1) : Y'.Fn) ^ (k : ℕ) * (ψ (eqn A'.D (below y₂.1) : Y'.Fn))⁻¹ ^ (k : ℕ) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hψ, one_pow]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
        map_mul, map_pow, map_inv₀, mul_pow, inv_pow]
      linear_combination (-(((eqn A.D (below y.1) : Y.Fn) ^ (k : ℕ))⁻¹ * ψ (r' i : Y'.Fn) * (u : Y.Fn) ^ (k : ℕ))) * hh
    have hck := (Base.valAt_zpow y.1 hc).2 (k : ℕ)
    simp only [zpow_natCast] at hck
    have hb0 := (Base.valAt_zpow y₂.1 hb).1
    have hc0 := (Base.valAt_zpow y.1 hc).1
    rw [key, valAt_mul' y.1 (unitAt_map hg hb).regAt hcr, valAt_map hg y.1 hb.regAt, hck, map_mul, map_pow,
      Real.log_mul (e.w.pos hb0).ne' (pow_pos (e.w.pos hc0) _).ne', Real.log_pow]
    linear_combination ((k : ℕ) : ℝ) * e1 + e2

end IsoTransport

theorem isArTop_of_adlIso : ∀ (F : Type) [Field F] [NumberField F] (C : GlobalTheory.TrueGeo.CxSt F) (Y Y' : Var F) (A : GlobalTheory.TrueGeo.Adl C Y) (A' : GlobalTheory.TrueGeo.Adl C Y') (φ : Y.X ≅ Y'.X) (ψ : Y'.Fn →+* Y.Fn) (u : Y.Fnˣ), AdlIso A A' φ ψ u → A.deg = A'.deg → ∀ t : ℝ, A'.IsArTop t → A.IsArTop t := by
  intro F _ _ C Y Y' A A' φ ψ u h hdeg t ht
  obtain ⟨M', L, k, cf, a, hI, ha, rfl⟩ := ht
  refine ⟨modelOfIso M' φ h.1.1 h.1.2.2.1, L, k, cf, a, induced_of_adlIso h hI, ha, ?_⟩
  rw [hdeg, h.2.1, h.1.2.2.1]

end GlobalTheory.ShFam.GalCarry
