import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ProdSplitConjugateEmbeddings
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MeasureTheory Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CxPts GlobalTheory.TopForm GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B L : LB Y} {O : Y.Opens}

def Weight.ofPick (hB : B.IsLB) (ψ : B.ι → CxPts p σ → ℝ) : Weight p σ B where
  isLB := hB
  φ i y := ψ (pick hB y) y - Real.log (‖gv p σ B (pick hB y) i y‖ ^ 2)
  trans i j y hi hj := by
    have h := mem_pick hB y
    rw [← gv_mul hB h hi hj, log_normSq_mul (gv_ne_zero h hi) (gv_ne_zero hi hj)]
    ring

theorem CompHS.cval_mem_fibSec (f : H0 p B O) : cval σ f ∈ fibSec p σ B := by
  refine ⟨fun i j y hi hj => ?_, fun i y h => ev_of_notMem (fun e => h (mem_ptsIn_inf.1 e).2) _⟩
  by_cases hO : y ∈ ptsIn p σ O
  · rw [cval_eq_val σ f i y hO hi, cval_eq_val σ f j y hO hj, H0.val_change y.1 i j hO hi hj]
    exact congrArg (· * _) (ev_eq (mem_ptsIn_inf.2 ⟨hi, hj⟩) _).symm
  · exact (ev_of_notMem (fun e => hO (mem_ptsIn_inf.1 e).1) _).trans
      ((mul_zero _).symm.trans (congrArg _ (ev_of_notMem (fun e => hO (mem_ptsIn_inf.1 e).1) _).symm))

namespace CompHS

def divVal (σ : k →+* ℂ) (ω : H0 p (LB.div B L) O) : (tens B (dual L)).ι → CxPts p σ → ℂ := cval σ ω

theorem divVal_mem (ω : H0 p (LB.div B L) O) : divVal σ ω ∈ fibSec p σ (tens B (dual L)) := by
  have h := cval_mem_fibSec (σ := σ) ω
  refine ⟨fun i j y hi hj => (h.1 i j y hi hj).trans (congrArg (· * _) ?_), h.2⟩
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  exact (ev_mul _ _ y).trans (Eq.trans (congrArg (_ * ·) ((ev_inv hy _).trans (Eq.symm ((ev_res _ hy _).trans
    ((ev_inv (mem_ptsIn_inf.2 ⟨(mem_ptsIn_inf.1 hi).2, (mem_ptsIn_inf.1 hj).2⟩) _).trans
      (congrArg (·⁻¹) (ev_res _ hy _).symm)))))) (ev_mul _ _ y).symm)

variable {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) (φ φ' : Weight p σ L)
  (ω : H0 p (LB.div K.bundle L) O)

def volDens (a : AlgChart p σ D) (y : CxPts p σ) : ℝ := a.topDens K φ.dual (divVal σ ω) y

def volMeasure : Measure (CxPts p σ) :=
  ((AnRead.all p σ D).topMeasure K φ.dual (divVal σ ω)).restrict (ptsIn p σ O)

variable {φ φ'}

theorem volDens_eq (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source) {i : K.bundle.ι} {j : L.ι}
    (hi : y ∈ ptsIn p σ (K.bundle.U i)) (hj : y ∈ ptsIn p σ (L.U j)) : volDens K φ ω a y =
      2 ^ D * (‖rv σ a.isFrame (K.isFrame i) y * cval σ ω (i, j) y‖ ^ 2 / Real.exp (-φ.φ j y)) := by
  rw [volDens, a.topDens_eq K φ.dual (divVal_mem ω) hy hi (b := j) hj, div_eq_mul_inv, ← Real.exp_neg]
  rfl

theorem volDens_pos (hω : NowhereZero ω) (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source)
    (hO : y ∈ ptsIn p σ O) : 0 < volDens K φ ω a y := by
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  have hm : y ∈ ptsIn p σ (O ⊓ (LB.div K.bundle L).U (_, _)) := mem_ptsIn_inf.2 ⟨hO, mem_ptsIn_inf.2 ⟨hi, hj⟩⟩
  have h₁ : cval σ ω (_, _) y ≠ 0 := (mem_ptsIn_basicOpen hm _).1 (mem_ptsIn.2
    ((Y.mem_basicOpen _ _ (mem_ptsIn.1 hm)).2 (hω _ (mem_ptsIn.1 hm).1 _ (mem_ptsIn.1 hm).2)))
  have h₂ := mul_ne_zero (rv_ne_zero a.isFrame (K.isFrame _) (a.source_subset hy) hi) h₁
  rw [volDens_eq K ω a hy hi hj]
  positivity

theorem volMeasure_compl : volMeasure K φ ω (ptsIn p σ O)ᶜ = 0 := by
  rw [volMeasure, Measure.restrict_apply (isOpen_ptsIn O).measurableSet.compl, compl_inter_self, measure_empty]

variable [SecondCountableTopology (CxPts p σ)]

theorem volMeasure_apply (a : AlgChart p σ D) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (h : A ⊆ a.e.source) :
    volMeasure K φ ω A = ∫⁻ v in a.e '' (A ∩ ptsIn p σ O), ENNReal.ofReal (volDens K φ ω a (a.e.symm v)) := by
  rw [volMeasure, Measure.restrict_apply hA]
  exact (AnRead.all p σ D).topMeasure_apply K _ _ a (hA.inter (isOpen_ptsIn O).measurableSet) (inter_subset_left.trans h)

theorem volMeasure_of_add {s : ℝ} (h : ∀ j, ∀ y ∈ ptsIn p σ O, y ∈ ptsIn p σ (L.U j) → φ'.φ j y = φ.φ j y + s) :
    volMeasure K φ' ω = ENNReal.ofReal (Real.exp s) • volMeasure K φ ω := by
  refine ext_of_cover _ (fun a : AlgChart p σ D => a.e.open_source) AlgChart.exists_mem_source fun a A hA hs => ?_
  have hA' := hA.inter (isOpen_ptsIn (p := p) (σ := σ) O).measurableSet
  rw [Measure.smul_apply, volMeasure_apply K ω a hA hs, volMeasure_apply K ω a hA hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_image a.e hA' (inter_subset_left.trans hs)) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  simp only [a.e.left_inv (hs hy.1)]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, volDens_eq K ω a (hs hy.1) hi hj, volDens_eq K ω a (hs hy.1) hi hj,
    h _ y hy.2 hj, neg_add, Real.exp_add, Real.exp_neg s]
  congr 1
  field_simp

theorem volMeasure_congr (h : ∀ j, ∀ y ∈ ptsIn p σ O, y ∈ ptsIn p σ (L.U j) → φ'.φ j y = φ.φ j y) :
    volMeasure K φ' ω = volMeasure K φ ω := by
  rw [volMeasure_of_add K ω (φ := φ) (s := 0) (by simpa using h)]
  simp

theorem volMeasure_pos (hω : NowhereZero ω) (hφ : ∀ j, ContinuousOn (φ.φ j) (ptsIn p σ O ∩ ptsIn p σ (L.U j)))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ O) : 0 < volMeasure K φ ω univ := by
  obtain ⟨a, ha⟩ := AlgChart.exists_mem_source (D := D) y
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  set i := pick K.isLB y
  set j := pick φ.isLB y
  let S := a.e.source ∩ (ptsIn p σ (a.U ⊓ K.bundle.U i) ∩ ptsIn p σ (O ⊓ (LB.div K.bundle L).U (i, j)))
  have hS : IsOpen S := a.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hO : S ⊆ ptsIn p σ O := fun z hz => (mem_ptsIn_inf.1 hz.2.2).1
  have hL : S ⊆ ptsIn p σ (L.U j) := fun z hz => (mem_ptsIn_inf.1 (mem_ptsIn_inf.1 hz.2.2).2).2
  have hc : ContinuousOn (volDens K φ ω a) S := (continuousOn_const.mul
    (((((continuousOn_ev _).mono fun _ hz => hz.2.1).mul ((continuousOn_ev _).mono fun _ hz => hz.2.2)).norm.pow 2).div
      ((hφ j).mono (subset_inter hO hL)).neg.rexp fun _ _ => (Real.exp_pos _).ne')).congr
    fun z hz => volDens_eq K ω a hz.1 (mem_ptsIn_inf.1 hz.2.1).2 (hL hz)
  have ho := a.e.isOpen_image_of_subset_source hS inter_subset_left
  have hm : MapsTo a.e.symm (a.e '' S) S := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [a.e.left_inv hz.1]
  have hc' := ENNReal.continuous_ofReal.comp_continuousOn (hc.comp (a.e.continuousOn_symm.mono
    (image_subset_iff.2 fun _ hz => a.e.map_source hz.1)) hm)
  refine lt_of_lt_of_le ?_ (measure_mono (subset_univ S))
  rw [volMeasure_apply K ω a hS.measurableSet inter_subset_left, inter_eq_left.2 hO, pos_iff_ne_zero]
  intro h
  have h₁ := (ae_restrict_iff' ho.measurableSet).1 ((lintegral_eq_zero_iff' (hc'.aemeasurable ho.measurableSet)).1 h)
  refine (ho.measure_pos volume ⟨_, y, ⟨ha, mem_ptsIn_inf.2 ⟨a.source_subset ha, hi⟩,
    mem_ptsIn_inf.2 ⟨hy, mem_ptsIn_inf.2 ⟨hi, hj⟩⟩⟩, rfl⟩).ne' (measure_mono_null ?_ (ae_iff.1 h₁))
  exact fun v hv hh => (ENNReal.ofReal_pos.2 (volDens_pos K ω hω a (hm hv).1 (hO (hm hv)))).ne' (hh hv)

example (y : CxPts (CanonLB.affStr k D) σ) (s : ℝ) :
    ∃ ω : H0 (CanonLB.affStr k D) (LB.div (CanonLB.affineSpace k D).bundle (LB.triv _)) ⊤, NowhereZero ω ∧
      0 < volMeasure (CanonLB.affineSpace k D) (Weight.ofFun (σ := σ) fun _ => s) ω univ ∧
      volMeasure (CanonLB.affineSpace k D) (Weight.ofFun (σ := σ) fun _ => s) ω =
        ENNReal.ofReal (Real.exp s) • volMeasure (CanonLB.affineSpace k D) (Weight.ofFun fun _ => 0) ω := by
  have : Smooth (CanonLB.affStr k D) := SmoothOfRelativeDimension.smooth D _
  let t : (LB.div (CanonLB.affineSpace k D).bundle (LB.triv _)).Sec := ⟨fun _ => 1, fun i j => by
    rw [map_one, map_one, mul_one]
    refine fun_ext_ger fun z hz => Eq.symm ((ger_resG (le_inf le_rfl le_rfl) z hz.1 _).symm.trans ?_)
    exact (congrArg _ (LB.resG_g_self (LB.isLB_div (CanonLB.affineSpace k D).isLB (LB.isLB_triv _)) i _)).trans
      ((map_one _).trans (map_one _).symm)⟩
  have ht : NowhereZero (H0.ofSec (CanonLB.affStr k D) ⊤ t) := fun z hz i hi => by
    rw [H0.germ_ofSec]; exact isUnit_one.map _
  exact ⟨_, ht, volMeasure_pos _ _ ht (fun _ => continuousOn_const) (mem_ptsIn_top (y := y)),
    volMeasure_of_add _ _ fun _ _ _ _ => (zero_add s).symm⟩

end CompHS

end General

namespace CompHS

open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (exOf wtOf lieFacZ modelWt homN)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Good

variable {Y T : Scheme.{0}} {p : Y ⟶ Sp c.F} {σ σ' : c.F →+* ℂ} {B : LB Y}

open Classical in

def goodPt (y : CxPts p σ) : CxPts p (goodOf c σ) :=
  ⟨if GoodEmb c σ then y.1 else spMap (starRingEnd ℂ) ≫ y.1, by
    have h : y.1 ≫ p = spMap σ := y.2
    change _ ≫ p = spMap _
    unfold goodOf
    split_ifs
    · exact h
    · rw [Category.assoc, h, spMap, spMap, spMap, ← Spec.map_comp]; rfl⟩

theorem goodPt_of_good (h : GoodEmb c σ) (y : CxPts p σ) : (goodPt y).1 = y.1 := if_pos h

theorem goodPt_of_not (h : ¬ GoodEmb c σ) (y : CxPts p σ) : (goodPt y).1 = spMap (starRingEnd ℂ) ≫ y.1 := if_neg h

theorem goodPt_mem {y : CxPts p σ} {W : Y.Opens} (h : y ∈ ptsIn p σ W) : goodPt y ∈ ptsIn p (goodOf c σ) W := by
  change ⊤ ≤ (goodPt y).1 ⁻¹ᵁ W
  by_cases hσ : GoodEmb c σ
  · rw [goodPt_of_good hσ]; exact h
  · rw [goodPt_of_not hσ]; exact FlagMod.le_preimage_comp _ h

theorem norm_ev_goodPt {y : CxPts p σ} {W : Y.Opens} (h : y ∈ ptsIn p σ W) (f : Γ(Y, W)) :
    ‖ev p _ W f (goodPt y)‖ = ‖ev p σ W f y‖ := by
  by_cases hσ : GoodEmb c σ
  · rw [ev, goodPt_of_good hσ, ev]
  · rw [ev_conj (goodPt_of_not hσ y) h, RCLike.norm_conj]

theorem goodPt_map {q : T ⟶ Sp c.F} {f : T ⟶ Y} {z : CxPts q σ} {y : CxPts p σ} (h : y.1 = z.1 ≫ f) :
    (goodPt y).1 = (goodPt z).1 ≫ f := by
  by_cases hσ : GoodEmb c σ
  · rw [goodPt_of_good hσ, goodPt_of_good hσ, h]
  · rw [goodPt_of_not hσ, goodPt_of_not hσ, h, Category.assoc]

theorem goodPt_conj {y : CxPts p σ} {y' : CxPts p ((starRingEnd ℂ).comp σ)}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : (goodPt y').1 = (goodPt y).1 := by
  by_cases hσ : GoodEmb c σ
  · rw [goodPt_of_good hσ, goodPt_of_not (CompHt.not_goodEmb_conj hσ), h, ← Category.assoc, spMap, ← Spec.map_comp]
    refine (congrArg (fun f => Spec.map f ≫ y.1) (?_ : _ = 𝟙 _)).trans (by rw [Spec.map_id, Category.id_comp])
    exact CommRingCat.hom_ext (RingHom.ext fun z => Complex.conj_conj z)
  · have h' := goodEmb_goodOf c σ
    rw [goodOf, if_neg hσ] at h'
    rw [goodPt_of_good h', goodPt_of_not hσ, h]

def atGood (φ : Weight p (goodOf c σ) B) : Weight p σ B where
  isLB := φ.isLB
  φ i y := φ.φ i (goodPt y)
  trans i j y hi hj := by
    rw [φ.trans i j _ (goodPt_mem hi) (goodPt_mem hj), CxPts.gv, norm_ev_goodPt (mem_ptsIn_inf.2 ⟨hi, hj⟩), CxPts.gv]

theorem isConj_atGood (φ : ∀ τ, Weight p τ B) (σ : c.F →+* ℂ) :
    (atGood (φ (goodOf c σ))).IsConj (atGood (φ (goodOf c ((starRingEnd ℂ).comp σ)))) := fun i y y' h _ => by
  have key : ∀ (τ τ' : c.F →+* ℂ) (z : CxPts p τ) (z' : CxPts p τ'), τ' = τ → z'.1 = z.1 →
      (φ τ').φ i z' = (φ τ).φ i z := by
    rintro τ _ z z' rfl e
    rw [Subtype.ext e]
  exact key _ _ _ _ (CompHt.goodOf_conj σ) (goodPt_conj h)

end Good

section Fac

variable {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)

open Classical in

def diagChar (e : Ix Dw → ℤ) (t : Ix Dw → (CAt σ)ˣ) : ℂ := toC (∏ ix, t ix ^ e ix).val

theorem diagChar_ne_zero (e : Ix Dw → ℤ) (t : Ix Dw → (CAt σ)ˣ) : diagChar e t ≠ 0 := Units.ne_zero (M₀ := ℂ) _

theorem diagChar_mul (e : Ix Dw → ℤ) (t t' : Ix Dw → (CAt σ)ˣ) : diagChar e (t * t') = diagChar e t * diagChar e t' := by
  simp only [diagChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]
  rfl

theorem diagChar_add (e e' : Ix Dw → ℤ) (t : Ix Dw → (CAt σ)ˣ) : diagChar (e + e') t = diagChar e t * diagChar e' t := by
  simp only [diagChar, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  rfl

theorem diagChar_one (e : Ix Dw → ℤ) : diagChar (σ := σ) e 1 = 1 := by
  simp only [diagChar, Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one]
  rfl

theorem diagChar_zero (t : Ix Dw → (CAt σ)ˣ) : diagChar 0 t = 1 := by
  simp only [diagChar, Pi.zero_apply, zpow_zero, Finset.prod_const_one, Units.val_one]
  rfl

def homFac (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) : ℝ :=
  lieFacZ Dw x (wtOf Dw la 0) * (U.X k).nfac (modelWt U (wtOf Dw la 0) k) w.1

theorem homFac_pos (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) : 0 < homFac U x la k w :=
  mul_pos (AllWt.lieFacZ_pos _ _) (BoundedSectionAlgebra.nfac_pos _ w.2 _)

theorem homFac_add (a b : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) :
    homFac U x (a + b) k w = homFac U x a k w * homFac U x b k w := by
  have e : wtOf Dw (a + b) 0 = wtOf Dw a 0 + wtOf Dw b 0 := AllWt.wtOf_add a b 0 0
  rw [homFac, e, AllWt.modelWt_add U (AllWt.even_wtOf a 0) (AllWt.even_wtOf b 0), BoundedSectionAlgebra.nfac_add _ w.2,
    AllWt.lieFacZ_add, mul_mul_mul_comm]
  rfl

theorem homN_eq_homFac (la : AllWt.Weight Dw) (f : Rul Xo c) (k : U.Comp) (w : (U.X k).dom) :
    homN U x (wtOf Dw la 0) f ⟨k, w.1⟩ = homFac U x la k w * ‖toC (evR Xo c f (U.un k w))‖ := by
  have e : rdU U f k w.1 = toC (evR Xo c f (U.un k w)) := dif_pos w.2
  change _ * (‖rdU U f k w.1‖ * (U.X k).nfac _ _) = _
  rw [e, homFac]
  ring

def genNorm (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ) : ℝ :=
  homFac U x la k w * ‖diagChar (exOf Dw la 0) t‖

theorem genNorm_pos (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ) :
    0 < genNorm U x la k w t := mul_pos (homFac_pos _ _ _ _ _) (norm_pos_iff.2 (diagChar_ne_zero _ _))

theorem genNorm_add (a b : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ) :
    genNorm U x (a + b) k w t = genNorm U x a k w t * genNorm U x b k w t := by
  rw [genNorm, homFac_add, exOf_add_zero, diagChar_add, norm_mul, mul_mul_mul_comm]
  rfl

variable {U}

theorem homFac_frBor (hσ : GoodEmb c σ) (hU : IsUnf U) (la : AllWt.Weight Dw) {k k' : U.Comp} {w : (U.X k).dom}
    {w' : (U.X k').dom} {t : Ix Dw → (CAt σ)ˣ} (ht : FrBor t (U.un k w) (U.un k' w')) :
    homFac U x la k' w' * ‖diagChar (exOf Dw la 0) t‖ = homFac U x la k w := by
  classical
  obtain ⟨γ, hγ, b, hb, e⟩ := (hU.2.2.2.1 k k' w w').1 ⟨t, ht⟩
  obtain rfl : k' = k := congrArg Sigma.fst e
  obtain ⟨w', hw'⟩ := w'
  obtain rfl : w' = rmul (lact γ w.1) b := eq_of_heq (Sigma.mk.inj e).2
  have hd := BorelDiag.norm_diag_eq_norm_bdiag E H Dw l Xo c σ r U hσ hU k' w γ hγ b hb hw' t ht
  have nat : ∀ a : (E →+* ℂ) × ℕ → ℕ, ‖diagChar (exZ Dw (wtZ a 0)) t‖ = ‖bchar (modelWt U (wtZ a 0) k') b‖ := fun a => by
    have h1 : diagChar (exZ Dw (wtZ a 0)) t =
        ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), toC (t (some ⟨τ, i⟩) : CAt σ) ^ a (τ, i) := by
      simp only [diagChar, AllWt.exZ_wtZ, zpow_natCast, Fintype.prod_option, Fintype.prod_sigma, ex, pow_zero, one_mul,
        Units.coe_prod, Units.val_pow_eq_pow_val]
      rfl
    rw [AllWt.modelWt_wtZ, BorelChar.bchar_laU_eq U hσ hU k' b hb a 0 0 rfl, h1]
    simp only [pow_zero, one_mul, norm_pow, norm_prod, hd]
  have hG : wtOf Dw la 0 + wtZ (fun i => (-(wtOf Dw la 0).1 i).toNat) 0 = wtZ (fun i => ((wtOf Dw la 0).1 i).toNat) 0 :=
    Prod.ext (funext fun i => by simp only [wtZ, Prod.fst_add, Pi.add_apply]; omega) rfl
  have h₁ := nat fun i => ((wtOf Dw la 0).1 i).toNat
  have h₂ := nat fun i => (-(wtOf Dw la 0).1 i).toNat
  rw [← hG, AllWt.modelWt_add U (AllWt.even_wtOf la 0) ⟨0, rfl⟩, BoundedSectionAlgebra.bchar_add _ hb, funext (exZ_add _ _),
    norm_mul, ← h₂] at h₁
  have h₃ := mul_right_cancel₀ (norm_ne_zero_iff.2 (diagChar_ne_zero _ t))
    (((norm_mul _ _).symm.trans (congrArg _ (diagChar_add _ _ t).symm)).trans h₁)
  have hγw := dom_lact (U.X k') w.2 ((U.X k').Γ_stab γ hγ)
  rw [homFac, homFac, exOf, h₃, mul_assoc, mul_comm (Data.nfac _ _ _),
    NormFactor.norm_bchar_mul_nfac_rmul _ _ hγw hb, NormFactor.nfacLact_holds r _ _ γ hγ _ w.2]

end Fac

end CompHS

end GlobalTheory
