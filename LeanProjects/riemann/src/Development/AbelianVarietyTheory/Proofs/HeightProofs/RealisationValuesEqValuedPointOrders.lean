import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHoldStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericSectionPointsInequivalentValuationsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemRangeOfValVLeOne

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RealisationValues

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Reg

section Val

def pullVal {L : Type} [Field L] (U : CDVR) (ι : L →+* U.Fr) : AddValuation L (WithTop ℤ) :=
  open Classical in
  AddValuation.of (fun x => if x = 0 then ⊤ else ((vV U.V (ι x) : ℤ) : WithTop ℤ)) (by simp)
    (by simp [vV_one'])
    (fun x y => by
      beta_reduce
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · subst hx; rw [zero_add]; exact min_le_right _ _
      by_cases hy : y = 0
      · subst hy; rw [add_zero]; exact min_le_left _ _
      simp only [hxy, hx, hy, if_false, map_add]
      have := min_le_vV_add (V := U.V) ((map_ne_zero ι).2 hx) ((map_ne_zero ι).2 hy)
        (by rw [← map_add]; exact (map_ne_zero ι).2 hxy)
      exact_mod_cast this)
    (fun x y => by
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      simp only [mul_ne_zero hx hy, hx, hy, if_false, map_mul]
      rw [vV_mul ((map_ne_zero ι).2 hx) ((map_ne_zero ι).2 hy)]
      push_cast; rfl)

theorem pullVal_of_ne {L : Type} [Field L] (U : CDVR) (ι : L →+* U.Fr) {x : L} (hx : x ≠ 0) :
    pullVal U ι x = ((vV U.V (ι x) : ℤ) : WithTop ℤ) := by
  simp [pullVal, hx]

theorem vV_zero' (U : CDVR) : vV U.V (0 : U.Fr) = 0 := by simp [vV]

theorem vLa_pos_iff' {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ≠ 0) :
    0 < vLa la (a : K) ↔ a ∈ la.asIdeal := by
  have h0 : la.valuation K (a : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact_mod_cast ha
  rw [← la.valuation_lt_one_iff_mem (K := K) a]
  rw [← WithZero.log_lt_log h0 one_ne_zero, WithZero.log_one, vLa]
  omega

theorem exists_vLa_eq_one {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ vLa la (a : K) = 1 := by
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  have h1 : la.valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
    rw [← hπ]; exact la.valuation_of_algebraMap π
  refine ⟨π, ?_, ?_⟩
  · rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  · rw [vLa, h1, WithZero.log_exp]; rfl

theorem over_and_ramIdx {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 K)) {e : ℕ} (he : 0 < e)
    (hv : ∀ a : K, a ≠ 0 → v (algebraMap K L a) = (((e : ℤ) * vLa la a : ℤ) : WithTop ℤ)) :
    ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := K) v la ∧ ReciprocityTheory.ChartRestriction.G.T0.ramIdx (K := K) v la = e := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  refine ⟨fun a => ?_, ?_⟩
  · by_cases ha : a = 0
    · subst ha; simp
    rw [hv _ (by exact_mod_cast ha), ← vLa_pos_iff' la ha]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
    exact mul_pos_iff_of_pos_left he'
  · refine IsLeast.csInf_eq ⟨?_, ?_⟩
    · obtain ⟨a, ha, h1⟩ := exists_vLa_eq_one la
      refine ⟨a, (vLa_pos_iff' la ha).1 (by omega), ha, ?_⟩
      rw [hv _ (by exact_mod_cast ha), h1, mul_one]
    · rintro n ⟨a, hm, ha, hn⟩
      rw [hv _ (by exact_mod_cast ha), WithTop.coe_eq_coe] at hn
      have := (vLa_pos_iff' la ha).2 hm
      nlinarith

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem generic_of_ne_zero (h : GenFrEx Xo c) (Z : Comp Xo c) (L : Type) [Field L] [Algebra c.F L]
    (y : FrPt Xo c L)
    (hZ : ∃ a n, ∃ f ∈ sec Xo c a n, evR Xo c f y ≠ 0 ∧ ∀ Z', Z' ≠ Z → evC h Z' f = 0)
    (hR : ∀ r : Om Z, r ≠ 0 → ∃ a n, ∃ f ∈ sec Xo c a n, ∃ g ∈ sec Xo c a n,
      evC h Z f = r * evC h Z g ∧ evR Xo c f y ≠ 0) :
    ∃ (ψ : Om Z →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ (genFr h Z) z ∧ FrBor t z y := by
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  obtain ⟨C, ψ0, z0, t', hz0, hb0⟩ := hA h L y
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c
  have e1 : ∀ a n, ∀ f ∈ sec Xo c a n,
      ((evR Xo c f C.y : C.R) : Om C.Z) = wchar (ex Dw a n) C.t * evC h C.Z f := fun a n f hf =>
    (GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf _ _ C.R.val _ _ C.gen).symm.trans
      (hL.wt a n f hf _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor)
  have e2 : ∀ a n, ∀ f ∈ sec Xo c a n,
      evR Xo c f y = wchar (ex Dw a n) t' * ψ0 (evR Xo c f C.y) := fun a n f hf => by
    rw [← GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf _ _ ψ0 _ _ hz0]
    exact hL.wt a n f hf _ t' _ _ (hL.test _ _) (hL.test _ _) hb0
  have hCZ : C.Z = Z := by
    by_contra hne
    obtain ⟨a, n, f, hf, h1, h2⟩ := hZ
    apply h1
    have : evR Xo c f C.y = 0 := Subtype.ext (by rw [e1 a n f hf, h2 _ hne, mul_zero]; rfl)
    rw [e2 a n f hf, this, map_zero, mul_zero]
  subst hCZ
  have hinj : Function.Injective ψ0 := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    obtain ⟨a, n, f, hf, g, hg, h1, h2⟩ := hR r (fun e => hr0 (Subtype.ext e))
    apply h2
    have : evR Xo c f C.y = r * evR Xo c g C.y := Subtype.ext (by
      rw [Subalgebra.coe_mul, e1 a n f hf, e1 a n g hg, h1]; ring)
    rw [e2 a n f hf, this, map_mul, hr, zero_mul, mul_zero]
  haveI : IsFractionRing C.R (Om C.Z) := IsFractionRing.of_field _ _ fun x => by
    obtain ⟨a, ha, b, hb, hb0, hx⟩ := C.frac x
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 hx⟩
  let ψ : Om C.Z →ₐ[c.F] L := IsFractionRing.liftAlgHom hinj
  have hψ : ψ.comp C.R.val = ψ0 := by
    ext r
    exact IsFractionRing.lift_algebraMap hinj r
  obtain ⟨z, hz⟩ := hL.bc _ _ ψ (genFr h C.Z)
  have m1 : FrMap ψ C.yg z0 := frMap_cancel _ _ _ C.R.val ψ C.y C.yg z0 C.gen (by rw [hψ]; exact hz0)
  have b1 := frBorBC _ _ ψ C.t _ _ z z0 C.bor hz m1
  exact ⟨ψ, z, _, hz, (G L).2.1 _ _ _ _ _ b1 hb0⟩

theorem ratio_of_generic (h : GenFrEx Xo c) (Z : Comp Xo c) (L : Type) [Field L] [Algebra c.F L]
    {y z : FrPt Xo c L} {ψ : Om Z →ₐ[c.F] L} {t : Ix Dw → Lˣ} (hz : FrMap ψ (genFr h Z) z) (hb : FrBor t z y)
    {a n} {f g : Rul Xo c} (hf : f ∈ sec Xo c a n) (hg : g ∈ sec Xo c a n) {r : Om Z}
    (hr : evC h Z f = r * evC h Z g) : evR Xo c f y = ψ r * evR Xo c g y := by
  obtain ⟨hL, -⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  have e : ∀ f ∈ sec Xo c a n, evR Xo c f y = wchar (ex Dw a n) t * ψ (evC h Z f) := fun f hf => by
    rw [evC, ← GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf _ _ ψ _ _ hz]
    exact hL.wt a n f hf _ t _ _ (hL.test _ _) (hL.test _ _) hb
  rw [e f hf, e g hg, hr, map_mul]; ring

theorem generic_int (h : GenFrEx Xo c) (Z : Comp Xo c) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
    (hZ : ∃ a n, ∃ f ∈ sec Xo c a n, evI y f ≠ 0 ∧ ∀ Z', Z' ≠ Z → evC h Z' f = 0)
    (hR : ∀ r : Om Z, r ≠ 0 → ∃ a n, ∃ f ∈ sec Xo c a n, ∃ g ∈ sec Xo c a n,
      evC h Z f = r * evC h Z g ∧ evI y f ≠ 0) :
    ∃ (ψ : Om Z →+* T.Fr) (hψ : ψ.comp (algebraMap c.F (Om Z)) = io),
      (letI := io.toAlgebra; ∃ (z : FrPt Xo c T.Fr) (t : Ix Dw → (T.Fr)ˣ),
        FrMap ({ ψ with commutes' := fun a => RingHom.congr_fun hψ a } : Om Z →ₐ[c.F] T.Fr) (genFr h Z) z ∧
          FrBor t z y.1) ∧
      ∀ a n, ∀ f ∈ sec Xo c a n, ∀ g ∈ sec Xo c a n, ∀ r, evC h Z f = r * evC h Z g → evI y f = ψ r * evI y g := by
  letI := io.toAlgebra
  obtain ⟨ψ, z, t, hz, hb⟩ := generic_of_ne_zero h Z T.Fr y.1 hZ hR
  exact ⟨ψ.toRingHom, RingHom.ext ψ.commutes, ⟨z, t, hz, hb⟩,
    fun a n f hf g hg r hr => ratio_of_generic h Z T.Fr hz hb hf hg hr⟩

theorem nval_eq_nval {T U : CDVR} {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {x : T.Fr} {y : U.Fr}
    (hxy : nval T.V e x = nval U.V e' y) : (x = 0 ↔ y = 0) ∧ (e' : ℤ) * vV T.V x = (e : ℤ) * vV U.V y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0
  · subst hx hy; simp [vV_zero']
  · rw [hx, nval_zero, nval_of_ne hy] at hxy
    exact absurd hxy.symm (EReal.coe_ne_top _)
  · rw [hy, nval_zero, nval_of_ne hx] at hxy
    exact absurd hxy (EReal.coe_ne_top _)
  · refine ⟨by simp [hx, hy], ?_⟩
    rw [nval_of_ne hx, nval_of_ne hy, EReal.coe_eq_coe_iff,
      div_eq_div_iff (by exact_mod_cast he.ne') (by exact_mod_cast he'.ne')] at hxy
    have : ((e' : ℤ) : ℝ) * (vV T.V x : ℝ) = ((e : ℤ) : ℝ) * (vV U.V y : ℝ) := by push_cast; linarith
    exact_mod_cast this

theorem int_eq_mul_nval {T : CDVR} {e r : ℕ} (he : 0 < e) (hr : 0 < r) {x : T.Fr} {o : ℤ}
    (ho : ((o : ℝ) : EReal) = ((((r : ℕ) : ℤ) : ℝ) : EReal) * nval T.V e x) :
    x ≠ 0 ∧ (e : ℤ) * o = (r : ℤ) * vV T.V x := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [nval_zero, EReal.mul_top_of_pos (by exact_mod_cast hr)] at ho
    exact EReal.coe_ne_top _ ho
  refine ⟨hx, ?_⟩
  rw [nval_of_ne hx, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at ho
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have : ((e : ℤ) : ℝ) * (o : ℝ) = ((r : ℤ) : ℝ) * (vV T.V x : ℝ) := by
    rw [ho]; push_cast; field_simp
  exact_mod_cast this

theorem ordC_valC (h : GenFrEx Xo c) (Z : Comp Xo c) (U : CDVR) (ι : Om Z →+* U.Fr) (δ : Ix Dw → ℤ) (a n)
    {f : Rul Xo c} (hf : evC h Z f ≠ 0) :
    ordC δ (pullVal U ι) (wtZ a n) (valC h a n f Z) = vV U.V (ι (evC h Z f)) + frW δ (wtZ a n) := by
  apply WithTop.coe_injective
  rw [valC, ordC_single _ _ _ hf, pullVal_of_ne _ _ hf]
  push_cast; rfl

theorem values_eq_ord (h1 : 1 ≤ Dw.p + Dw.q) (h2 : ∀ p : ℕ, p.Prime → l.GoodAt p) (h3 : l.A = 1)
    (h : GenFrEx Xo c) (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (U : CDVR) (ι : Om Z →+* U.Fr)
    {ep : ℕ} (hep : 0 < ep) {Wt : Type} (wa : Wt → (E →+* ℂ) × ℕ → ℕ) (wn : Wt → ℕ)
    (M : Wt → Submodule c.F (Rul Xo c)) (hM : ∀ w, ∀ F : M w, F.1 ∈ sec Xo c (wa w) (wn w))
    (ev : ∀ w, M w → U.Fr) (p : valSet Xo c (trivialClassCondition Xo c) la)
    (hv : ∀ w (F : M w), p.1 F.1 = nval U.V ep (ev w F))
    (hone : ∃ a, vV U.V (ι a) = 1)
    (hrat : ∀ w (F F' : M w), ι (evC h Z F.1) * ev w F' = ι (evC h Z F'.1) * ev w F)
    (hsp : ∀ w (F : M w), ∃ F' : M w, evC h Z F'.1 = evC h Z F.1 ∧ ∀ Z', Z' ≠ Z → evC h Z' F'.1 = 0)
    (hR : ∀ r : Om Z, ∃ w, ∃ F F' : M w, evC h Z F'.1 ≠ 0 ∧ ev w F' ≠ 0 ∧ evC h Z F.1 = r * evC h Z F'.1)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hδ : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) :
    ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete (pullVal U ι) ∧ ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) (pullVal U ι) la ∧
      ∀ w (F : M w), evC h Z F.1 ≠ 0 → ev w F ≠ 0 ∧ vV U.V (ev w F) =
        ordC (δ Z (pullVal U ι)) (pullVal U ι) (wtZ (wa w) (wn w)) (valC h (wa w) (wn w) F.1 Z) := by
  obtain ⟨_, ⟨_, T₁, io₁, e₁, ho₁, y₁, _, _, _, rfl⟩, rfl⟩ := p
  have hv₁ : ∀ w (F : M w), (evI y₁ F.1 = 0 ↔ ev w F = 0) ∧
      (ep : ℤ) * vV T₁.V (evI y₁ F.1) = (e₁ : ℤ) * vV U.V (ev w F) := fun w F => nval_eq_nval ho₁.1 hep (hv w F)
  have hev : ∀ w (F F' : M w) (r : Om Z), evC h Z F'.1 ≠ 0 → evC h Z F.1 = r * evC h Z F'.1 →
      ev w F = ι r * ev w F' := fun w F F' r h0 hr => by
    have := hrat w F F'
    rw [hr, map_mul] at this
    exact mul_left_cancel₀ ((map_ne_zero ι).2 h0) (by linear_combination -this)
  obtain ⟨w₀, -, F₀, hF₀, hF₀', -⟩ := hR 1
  obtain ⟨G₀, hG₀, hG₀'⟩ := hsp w₀ F₀
  have hG₀v : ev w₀ G₀ ≠ 0 := by
    rw [hev w₀ G₀ F₀ 1 hF₀ (by rw [hG₀, one_mul]), map_one, one_mul]; exact hF₀'
  obtain ⟨ψ₁, hψ₁, hg₁, hr₁⟩ := generic_int h Z T₁ io₁ y₁
    ⟨_, _, _, hM _ G₀, fun e => hG₀v ((hv₁ _ _).1.1 e), hG₀'⟩ (fun r hr => by
      obtain ⟨w, F, F', a1, a2, a3⟩ := hR r
      refine ⟨_, _, _, hM _ F, _, hM _ F', a3, fun e => ?_⟩
      have := (hv₁ _ _).1.1 e
      rw [hev w F F' r a1 a3] at this
      exact mul_ne_zero ((map_ne_zero ι).2 hr) a2 this)
  subst hψ₁
  have hep' : (ep : ℤ) ≠ 0 := by exact_mod_cast hep.ne'
  have he₁' : (e₁ : ℤ) ≠ 0 := by exact_mod_cast ho₁.1.ne'
  have k₁ : ∀ r : Om Z, (ep : ℤ) * vV T₁.V (ψ₁ r) = (e₁ : ℤ) * vV U.V (ι r) := fun r => by
    by_cases hr : r = 0
    · subst hr; simp [vV_zero']
    obtain ⟨w, F, F', a1, a2, a3⟩ := hR r
    have b1 := (hv₁ w F).2
    have b2 := (hv₁ w F').2
    rw [hr₁ _ _ _ (hM _ F) _ (hM _ F') r a3, hev w F F' r a1 a3,
      vV_mul ((map_ne_zero ψ₁).2 hr) (fun e => a2 ((hv₁ _ _).1.1 e)), vV_mul ((map_ne_zero ι).2 hr) a2] at b1
    linear_combination b1 - b2
  have hnd : ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete (pullVal U ι) := by
    refine ⟨fun a ha => by rw [pullVal_of_ne _ _ ha]; exact WithTop.coe_ne_top, ?_⟩
    obtain ⟨a, ha⟩ := hone
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp [vV_zero'] at ha
    exact ⟨a, by rw [pullVal_of_ne _ _ ha0, ha]; rfl⟩
  obtain ⟨hov, hram⟩ := over_and_ramIdx (pullVal U ι) la hep (fun a ha => by
    rw [pullVal_of_ne _ _ ((map_ne_zero _).2 ha)]
    congr 1
    have b1 := k₁ (algebraMap c.F (Om Z) a)
    have b2 : vV T₁.V (ψ₁ (algebraMap c.F (Om Z) a)) = _ := ho₁.2 a
    rw [b2] at b1
    exact mul_left_cancel₀ he₁' (by linear_combination -b1))
  refine ⟨hnd, hov, ?_⟩
  obtain ⟨⟨_, T₂, io₂, e₂, ho₂, y₂, _, _, _, rfl⟩, hy₂⟩ := hδ Z _ la hnd hov
  rw [hram] at hy₂
  have hv₂ : ∀ w (F : M w), evC h Z F.1 ≠ 0 → evI y₂ F.1 ≠ 0 ∧
      (e₂ : ℤ) * ordC (δ Z (pullVal U ι)) (pullVal U ι) (wtZ (wa w) (wn w)) (valC h (wa w) (wn w) F.1 Z) =
        (ep : ℤ) * vV T₂.V (evI y₂ F.1) := fun w F hF =>
    int_eq_mul_nval ho₂.1 hep (hy₂ _ _ _ (hM w F) hF)
  obtain ⟨ψ₂, hψ₂, hg₂, hr₂⟩ := generic_int h Z T₂ io₂ y₂
    ⟨_, _, _, hM _ G₀, (hv₂ _ G₀ (hG₀ ▸ hF₀)).1, hG₀'⟩ (fun r hr => by
      obtain ⟨w, F, F', a1, -, a3⟩ := hR r
      exact ⟨_, _, _, hM _ F, _, hM _ F', a3, (hv₂ _ F (a3 ▸ mul_ne_zero hr a1)).1⟩)
  subst hψ₂
  have he₂' : (e₂ : ℤ) ≠ 0 := by exact_mod_cast ho₂.1.ne'
  have k₂ : ∀ r : Om Z, (ep : ℤ) * vV T₂.V (ψ₂ r) = (e₂ : ℤ) * vV U.V (ι r) := fun r => by
    by_cases hr : r = 0
    · subst hr; simp [vV_zero']
    obtain ⟨w, F, F', a1, a2, a3⟩ := hR r
    have a4 : evC h Z F.1 ≠ 0 := a3 ▸ mul_ne_zero hr a1
    have b1 := (hv₂ w F a4).2
    have b2 := (hv₂ w F' a1).2
    rw [ordC_valC h Z U ι _ _ _ a1] at b2
    rw [ordC_valC h Z U ι _ _ _ a4, hr₂ _ _ _ (hM _ F) _ (hM _ F') r a3, a3, map_mul,
      vV_mul ((map_ne_zero ψ₂).2 hr) (hv₂ w F' a1).1,
      vV_mul ((map_ne_zero ι).2 hr) ((map_ne_zero ι).2 a1)] at b1
    linear_combination b2 - b1
  intro w F hF
  obtain ⟨c1, c2⟩ := Proportional.proportional_values E H Dw l Xo c h1 h2 h3 h Z T₁ T₂ ψ₁ ψ₂ y₁ y₂ e₁ e₂ ho₁.1 ho₂.1
    hg₁ hg₂ (by
      obtain ⟨a, ha⟩ := hone
      refine ⟨a, fun e => ?_⟩
      have := k₁ a
      rw [e, ha] at this
      exact he₁' (by linear_combination -this))
    (fun r => mul_left_cancel₀ hep' (by linear_combination (e₂ : ℤ) * k₁ r - (e₁ : ℤ) * k₂ r)) _ _ _ (hM w F)
  refine ⟨fun e => hF (c1.1 ((hv₁ w F).1.2 e)), mul_left_cancel₀ (mul_ne_zero he₁' he₂') ?_⟩
  linear_combination (ep : ℤ) * c2 - (e₂ : ℤ) * (hv₁ w F).2 - (e₁ : ℤ) * (hv₂ w F hF).2

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem exists_gen_ne_zero {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF}
    {la : HeightOneSpectrum (𝓞 B.KO)} {ζ : PtsG G la} {y : E.Pt' la} (hs : SecPt ζ y) :
    ∃ i, hs.ev (emb (xplus X E hM) la G.N (X.inc wL (G.w i))) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply hs.s0.ne_zero
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Algebra.smul_def, map_mul]
  exact mul_eq_zero_of_right _ (hc k)

set_option maxHeartbeats 4000000 in

theorem exists_ratio {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (hB : BIRSt h j hj hG G) (Z : Comp (T.Q.Xo j) T.Q.c) (i : Fin G.N)
    (hi : evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0) (a : Om Z) :
    ∃ k, ∃ p q : (recB h.toLawsCore).Cusp j (addL (wt0 D j) wL (k + 1)),
      evC hG Z ((q : (recB h.toLawsCore).Cusp j _) : T.R j) ≠ 0 ∧
      evC hG Z ((p : (recB h.toLawsCore).Cusp j _) : T.R j) =
        a * evC hG Z ((q : (recB h.toLawsCore).Cusp j _) : T.R j) := by
  have hw1 : ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j) ∈ cutR T.C j (addL (wt0 D j) wL 1) := by
    rw [add_zero_weight_one_eq]
    exact (G.w i).2
  obtain ⟨k, g, Pw, hP, hne, he⟩ := hB Z a
  have hg : (g : T.R j) ∈ cutR T.C j (addL (wt0 D j) wL k) := by
    rw [addL, zero_weight_add]
    exact g.2
  have hq := esec_hom_mem h hj (fun i => ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun i => (G.w i).2) (Pw * MvPolynomial.X i) (hP.mul (MvPolynomial.isHomogeneous_X _ i))
  have hv := esec_evC_aeval h hj hG hT Z
    (fun i => ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) (Pw * MvPolynomial.X i)
  rw [map_mul (MvPolynomial.aeval fun i => evC hG Z _), MvPolynomial.aeval_X] at hv
  refine ⟨k, ⟨_, esec_mem_mulL h hj hg hw1⟩, ⟨_, hq⟩, ?_, ?_⟩
  · exact fun h0 => mul_ne_zero hne hi (hv.symm.trans h0)
  · refine Eq.trans ?_ (congrArg (fun t => a * t) hv).symm
    refine (map_mul (evCAlg hG hT Z) _ _).trans ?_
    rw [evCAlg_apply, evCAlg_apply, ← mul_assoc, he]

end Record

end GlobalTheory.RealisationValues

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.RealisationValues.values_eq_orders : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → ∀ (δ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (T.Q.Dw j) → ℤ), OrdTie hG δ (trivialClassCondition (T.Q.Xo j) T.Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) → ∀ la (ζ : PtsG G la), ∃ (Z : Comp (T.Q.Xo j) T.Q.c) (v : AddValuation (Om Z) (WithTop ℤ)), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v ∧ ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := T.Q.c.F) v la ∧ ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), (evC hG Z F.1 = 0 → (hw la ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = 0) ∧ (evC hG Z F.1 ≠ 0 → (hw la ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0 ∧ vV (hw la ζ).T.V ((hw la ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) = ordC (δ Z v) v (wtZ (wtA w) w.n) (valC hG (wtA w) w.n F.1 Z)) := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hI hC hB y hw _ _ δ hδ la ζ
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold _ _ _ _ (T.Q.Xo j) T.Q.c).1.test _ _
  obtain ⟨n1, n2, -, -, -, -, n3⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨n4, n5, -⟩ := n3 j hj
  obtain ⟨Zc, ι, h1, h2, h3, -⟩ := GlobalTheory.T.generic_section_points_inequivalent_valuations D T h j hj hG hT ka wL wF G S g0 la hH hI hC hB (y la) (hw la)
  obtain ⟨i, hi⟩ := GlobalTheory.RealisationValues.exists_gen_ne_zero (hw la ζ).toSecPt
  have hL : ∀ k, ∃ u : (recB h.toLawsCore).Cusp j (addL (wt0 D j) wL (k + 1)),
      (hw la ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc _ u)) ≠ 0 := fun k => by
    rw [← esecW_eq]
    refine ⟨esecPow h hj (G.w i) k, ?_⟩
    rw [esec_inc_pow]
    exact fun h0 => pow_ne_zero (k + 1) hi
      (((map_pow ((hw la ζ).ev.comp (emb (recPlus h j hj) la G.N)) _ _).symm).trans h0)
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.RealisationValues.values_eq_ord (n4 ▸ n5) n1 n2 hG (Zc ζ) la (hw la ζ).T (ι ζ)
    (hw la ζ).ep_pos (Wt := WeightFamilies.Wt D j) wtA (fun w => w.n) (fun w => cutR T.C j w)
    (fun w F => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j w F.2))
    (fun w F => (hw la ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) (y la ζ)
    (fun w F => (extAll_vAt_inc h j hj la (y la ζ) w F).symm.trans ((hw la ζ).hv w F))
    (h1 ζ) (h3 ζ) (hC (Zc ζ))
    (fun r => by
      obtain ⟨k, p, q, a1, a2⟩ := GlobalTheory.RealisationValues.exists_ratio h hj hG hT G hB (Zc ζ) i
        (fun h0 => hi (h2 ζ wL (G.w i) h0)) r
      obtain ⟨u, hu⟩ := hL k
      refine ⟨_, p, q, a1, fun e => ?_, a2⟩
      have := h3 ζ _ q u
      exact mul_ne_zero ((map_ne_zero _).2 a1) hu (this.trans (mul_eq_zero_of_right _ e))) δ hδ
  exact ⟨Zc ζ, _, c1, c2, fun w F => ⟨h2 ζ w F, c3 w F⟩⟩
