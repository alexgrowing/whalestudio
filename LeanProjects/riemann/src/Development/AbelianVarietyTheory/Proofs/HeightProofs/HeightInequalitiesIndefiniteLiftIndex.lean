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
import Formalism.LocalToGlobal.ProjectiveLattices.ProdInLatPf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapDivFinStLocDataOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwise
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NotGoodConj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupBddAndSupREqSupN
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LawBddDataOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamiliesStatement
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RamOverZRealPos
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsUnitOfVVEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SupCLeISupGeneric
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LengthsAtPrimesLeFunctionFieldDataOfCurveStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrdersAuxiliaryFormAtPrimesEqFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotRestrDensityRescale
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCBaseValAtCx
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndependentDifferentialsRatiosOfTrdegValues
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ChosenFormsRestrictBasisFunctionField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.T0 (meanK PT)

namespace GlobalTheory.HeightTop

theorem nonempty_place (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩

theorem meanK_le_const {K : Type} [Field K] [NumberField K] {F : (K →+* ℂ) → ℝ} {b : ℝ} (h : ∀ sg, F sg ≤ b) :
    meanK F ≤ b := by
  unfold meanK
  have hn : (0 : ℝ) < Fintype.card (K →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact_mod_cast Module.finrank_pos
  rw [div_le_iff₀ hn]
  calc ∑ sg, F sg ≤ ∑ _sg : K →+* ℂ, b := Finset.sum_le_sum fun sg _ => h sg
    _ = b * Fintype.card (K →+* ℂ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

section Weights

variable {D : D7} {j : ℕ}

theorem extendByZero_add_eq_mul_of_forall {p : ℕ} {f g k : Fin p → ℕ} {m : ℕ} (h : ∀ i, f i + g i = m * k i) (i : ℕ) :
    ext0 f i + ext0 g i = m * ext0 k i := by
  unfold ext0; split_ifs
  · exact h _
  · simp

theorem wtA_add_eq {a b w : WeightFamilies.Wt D j} {m : ℕ} (hP : ∀ τ i, a.aP τ i + b.aP τ i = m * w.aP τ i)
    (hM : ∀ τ i, a.aM τ i + b.aM τ i = m * w.aM τ i) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA a x + wtA b x = m * wtA w x := by
  simp only [wtA, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 := extendByZero_add_eq_mul_of_forall (hP t) x.2
  have h2 := extendByZero_add_eq_mul_of_forall (hM t) x.2
  split_ifs <;> simp only [mul_add, mul_zero, add_zero, zero_add] <;> omega

theorem wtA_wscalar (n : ℕ) (hn : Even n) (x : (D.host.E →+* ℂ) × ℕ) : wtA (wscalar D j n hn) x = 0 := by
  simp [wtA, wscalar, ext0]

theorem wtZ_wEt (i : ℕ) :
    wtZ (wtA (wEt D j i)) (wEt D j i).n = (i * WeightAlgebra.g0 D) • wtZ (E := D.host.E) 0 1 := by
  refine Prod.ext (funext fun x => ?_) ?_
  · simp [wtZ, wEt, wtA_wscalar]
  · show ((WeightAlgebra.g0 D * i : ℕ) : ℤ) = (i * WeightAlgebra.g0 D) • ((1 : ℕ) : ℤ)
    rw [nsmul_eq_mul]; push_cast; ring

theorem weightSumVector_firstGeneratorWeight {wL w1 : WeightFamilies.Wt D j} (h : IsDoubledWeightWithShift wL w1 wL.n) :
    wtZ (wtA w1) w1.n = (2 : ℕ) • (wtZ (wtA wL) wL.n - wtZ (E := D.host.E) 0 1) := by
  refine Prod.ext (funext fun x => ?_) ?_
  · have := wtA_add_eq (a := w1) (b := wscalar D j 0 ⟨0, rfl⟩) (w := wL) (m := 2)
      (fun τ i => by simpa [wscalar] using h.2.1 τ i) (fun τ i => by simpa [wscalar] using h.2.2 τ i) x
    rw [wtA_wscalar 0 ⟨0, rfl⟩ x, add_zero] at this
    show (wtA w1 x : ℤ) = (2 : ℕ) • ((wtA wL x : ℤ) - ((0 : ℕ) : ℤ))
    rw [this, nsmul_eq_mul]; push_cast; ring
  · have := h.1
    show (w1.n : ℤ) = (2 : ℕ) • ((wL.n : ℤ) - ((1 : ℕ) : ℤ))
    rw [nsmul_eq_mul]; push_cast; omega

theorem weightSumVector_secondGeneratorWeight_definite {wL wF w2 : WeightFamilies.Wt D j} (h : IsG2 wL wF w2) :
    wtZ (wtA w2) w2.n = (WeightFamilies.dimY D j + 4 : ℕ) • wtZ (wtA wL) wL.n - wtZ (wtA wF) wF.n := by
  refine Prod.ext (funext fun x => ?_) ?_
  · have := wtA_add_eq h.2.1 h.2.2 x
    show (wtA w2 x : ℤ) = (WeightFamilies.dimY D j + 4 : ℕ) • (wtA wL x : ℤ) - (wtA wF x : ℤ)
    rw [nsmul_eq_mul, eq_sub_iff_add_eq]; exact_mod_cast this
  · have := h.1
    show (w2.n : ℤ) = (WeightFamilies.dimY D j + 4 : ℕ) • (wL.n : ℤ) - (wF.n : ℤ)
    rw [nsmul_eq_mul, eq_sub_iff_add_eq]; exact_mod_cast this

end Weights

section Rec

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

theorem nzAt_of_nonZeroComp (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F) : NZAt hG (F : T.R j) := by
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  intro Z h0
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, e1, e2⟩ := hC Z wL (G.w k)
  obtain ⟨H, hH⟩ := (recPlus h j hj).inc_mul u wL F g
  have hH0 : H = 0 := by
    refine hV _ H fun Z' => ?_
    have e := congrArg (formsEvR j hG hT Z') hH
    erw [map_mul, formsEvR_inc h j hj hG hT Z' u F, formsEvR_inc h j hj hG hT Z' wL g,
      formsEvR_inc h j hj hG hT Z' _ H] at e
    rw [← e]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [e2 Z' hZ, mul_zero]
  rw [hH0, map_zero] at hH
  have hg := hF wL g hH
  apply hk
  rw [← e1, hg]
  exact evC_zero hG Z

theorem log_iSup_le [Fintype (Comp (T.Q.Xo j) T.Q.c)] (hV : GenValInjSt h j hG)
    {fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ}
    {yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))}
    (hfn : FnNe (T.Q.Xo j) T.Q.c fn) (hPT : PTNe (T.Q.Xo j) T.Q.c) (hcx : ValAtCx hG yP)
    {w : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (hB : SupBdd (T.Q.Xo j) T.Q.c fn (wtA w) w.n F.1 ∧
      ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA w) w.n F.1 = (recB h.toLawsCore).supN j w sg F) (σ : T.Q.c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp (T.Q.Xo j) T.Q.c, PT (Ω := Om Z) σ),
        nrmC fn (yP p.1) (wtZ (wtA w) w.n) (valC hG (wtA w) w.n F.1 p.1) p.2) ≤
      Real.log ((recB h.toLawsCore).supN j w σ F) := by
  by_cases hN : NZSome hG F.1
  · rw [← hB.2 σ]
    exact log_supN_le hfn hPT hcx (cusp_le_sec _ _ (T.U j) _ _ (cutR_le T.C j w F.2)) hB.1 hN σ
  · have hz : ∀ Z, evC hG Z F.1 = 0 := fun Z => by
      by_contra h0
      exact hN ⟨Z, h0⟩
    have hF : F = 0 := hV w F hz
    have e1 : (recB h.toLawsCore).supN j w σ F = 0 := ((recB h.toLawsCore).supN_eq_zero _ _ _ _).2 hF
    have e2 : ∀ p : (Σ Z : Comp (T.Q.Xo j) T.Q.c, PT (Ω := Om Z) σ),
        nrmC fn (yP p.1) (wtZ (wtA w) w.n) (valC hG (wtA w) w.n F.1 p.1) p.2 = 0 := fun p => by
      unfold valC
      rw [nrmC_single, hz, map_zero, norm_zero, zero_mul]
    rw [e1]
    simp only [e2, Real.iSup_const_zero, le_refl]

end Rec

section Integral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ord_nonneg_of_regP {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hreg : regular₂ Xo c U) {h : GenFrEx Xo c}
    {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    (hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdom : Dom a n) {F : Rul Xo c} (hFC : F ∈ cusp Xo c U a n) (hF : IntAlg F)
    [Fintype (Comp Xo c)]
    {d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)}
    {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)} (hA : d.admitted Z v) (hne : evC h Z F ≠ 0) :
    0 ≤ ordC (δ Z v) v (wtZ a n) (valC h a n F Z) := by
  have hFs := cusp_le_sec Xo c U a n hFC
  have key : (0 : EReal) ≤ (((ordC (δ Z v) v (wtZ a n) (valC h a n F Z) : ℤ) : ℝ) : EReal) := by
    obtain ⟨hd, ⟨la, ho, -⟩ | ⟨ht, -⟩⟩ := hA
    · obtain ⟨y, hy⟩ := hT Z v la hd ho
      rw [hy a n F hFs hne]
      exact mul_nonneg (by exact_mod_cast ramIdx_nonneg ho)
        (hreg.int hdom hFC hF la _ (vAtV_mem_valSet (fun _ _ _ h => h) y))
    · obtain ⟨q, hq⟩ := hTQ Z v hd ht
      rw [hq a n F hFs hne]
      have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
        refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
        obtain ⟨u, hu⟩ := q.triv a ha
        rw [← hu]
        exact extVal_unit_zero q.T u
      exact (hreg.1.1 ⟨(a, n), hdom⟩ ⟨F, hFC⟩ fun la y => hF la y.1 y.2).2 ⟨_, hqT⟩
  exact_mod_cast key

end Integral

theorem heights_indefinite :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → FnAlgClosed (T.Q.Xo j) T.Q.c → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → ∀ (c th : ℝ) (w1 : WeightFamilies.Wt D j) (t1 : (recB h.toLawsCore).Cusp j w1), IsDoubledWeightWithShift wL w1 wL.n → t1 ∈ (recB h.toLawsCore).Mlat j w1 → (recPlus h j hj).NonZeroComp w1 t1 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w1 σ t1) ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → 0 < G.iet → G.et ∈ (recB h.toLawsCore).Mlat j _ → (recPlus h j hj).NonZeroComp _ G.et → (∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ G.et) / G.iet ≤ Pet) → 0 ≤ c → c * (WeightAlgebra.g0 D : ℝ) ≤ 1 / 2 → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ))) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ) + c * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x) → EtArch h th tableLineDegreeTwo j G.iet G.et → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hV hC hB y hw hcur htie hjm hac hD3 hn0 hIB large₂ Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL nus w2 t2 hTW hTT hthM hG2 ht2M ht2N ht2S hH1 hPN hLAM hLC hsz hDF hrw hnK hrd p1 p2 p3 p4 p5 p6 p7 p8 p9 hPH c th w1 t1 hG1 ht1M ht1N ht1S hi hetM hetN hetS hc0 hcg hcomb hI2 harch
  classical
  haveI : Nonempty (HeightOneSpectrum (𝓞 T.Q.c.F)) := nonempty_place _
  have hgt : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  have hx : 0 < xiR D := (GlobalTheory.PinNum.xiR_pos_le_one D T.Q h.pins.1).1
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ => h.unf j hj σ hσ
  obtain ⟨hkfg, ⟨d0, hd0, hd0'⟩, htr, hne, δ, hTQ, hTQZ, hTOn, hT, hFr⟩ := Ties.ordTies_of_pins D T.Q h.pins j hj hG
  have hreg := h.reg j hj
  obtain ⟨fn, hpin, hfn⟩ := GlobalTheory.FrameNorm.Existence.exists_pinned _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r _ hU (xiR D) hx
  obtain ⟨yP, hyP, hcx, -⟩ := GlobalTheory.Reg.exists_cBase_valAtCx _ _ _ _ (T.Q.Xo j) T.Q.c
    (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1 hG
  have hconj := (GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r _ hU (xiR D) fn hx hpin
    hG yP hyP).1
  have hsup := (GlobalTheory.FrameNorm.RecSup.supBdd_and_supR_eq_supN D T h j hj fn hpin).2.1
  have hfg := fnFG_of _ _ hkfg
  have hPT := ptNe_of_fnFG hfg
  have hdim : WeightFamilies.dimY D j = (T.Q.Dw j).dim + Nat.card (FlagVar (T.Q.Dw j)) := by
    obtain ⟨Z⟩ := hne
    have e := (hd0 Z).symm.trans ((GlobalTheory.Reg.kap_fg_trdeg _ _ _ _ (T.Q.Xo j) T.Q.c).2 Z)
    have e' : d0 = (T.Q.Dw j).dim := by exact_mod_cast e
    rw [← hd0', e']
  choose k0 hk0 hk0' using hH.2.1.2
  obtain ⟨N, hN⟩ : ∃ N, N + 1 = G.N := by
    obtain ⟨Z⟩ := hne
    exact ⟨G.N - 1, by have := (k0 Z).2; omega⟩
  let eN : Fin (N + 1) ≃ Fin G.N := finCongr hN
  let wR : Fin (N + 1) → T.R j := fun k => (G.w (eN k)).1
  let jc : Comp (T.Q.Xo j) T.Q.c → Fin (N + 1) := fun Z => eN.symm (k0 Z)
  let wsize : WTZ D.host.E → ℝ := fun g => if g = wtZ (wtA wL) wL.n then wL.size else wF.size
  have hsL : wsize (wtZ (wtA wL) wL.n) = wL.size := if_pos rfl
  have hsF : wsize (wtZ (wtA wF) wF.n) = wF.size := by
    by_cases e : wtZ (wtA wF) wF.n = wtZ (wtA wL) wL.n
    · have e1 : wF = wL := by
        refine GlobalTheory.LowerBoundCompare.wt_ext T.Q h.pins.1 (funext fun x => ?_) ?_
        · have : (wtA wF x : ℤ) = wtA wL x := congrFun (congrArg Prod.fst e) x
          exact_mod_cast this
        · have : (wF.n : ℤ) = wL.n := congrArg Prod.snd e
          exact_mod_cast this
      rw [e, hsL, e1]
    · exact if_neg e
  have hwb : ∀ Z, evC hG Z (wR (jc Z)) ≠ 0 := fun Z => by
    simp only [wR, jc, Equiv.apply_symm_apply]
    exact hk0 Z
  have hcu : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), F.1 ∈ T.cuspA j (wtA w) w.n :=
    fun w F => cutR_le T.C j w F.2
  have hse : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n :=
    fun w F => cusp_le_sec _ _ (T.U j) _ _ (hcu w F)
  have hin : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), F ∈ (recB h.toLawsCore).Mlat j w → IntAlg F.1 :=
    fun w F hF => hF
  have hetZ := nzAt_of_nonZeroComp h j hj hG hV hC G hH.2.1 _ hetN
  have h1Z := nzAt_of_nonZeroComp h j hj hG hV hC G hH.2.1 _ ht1N
  have h2Z := nzAt_of_nonZeroComp h j hj hG hV hC G hH.2.1 _ ht2N
  have huet := wtZ_wEt (D := D) (j := j) G.iet
  have hu1 := weightSumVector_firstGeneratorWeight hG1
  have hu2 := weightSumVector_secondGeneratorWeight_definite hG2
  have hnz : NoCommonZero (T.Q.Xo j) T.Q.c wR := by
    intro k _ _ _ z
    obtain ⟨i, hi⟩ := hH.2.1.1 k z
    exact ⟨eN.symm i, by simpa only [wR, Equiv.apply_symm_apply] using hi⟩
  have hcomb' : CombAlg (T.Q.Xo j) T.Q.c wR G.et.1 nus (c / (2 * (G.iet : ℝ))) := by
    intro la v hv
    have e : (⨅ k, v (wR k)) = ⨅ k, v (G.w k).1 := eN.iInf_comp (g := fun k => v (G.w k).1)
    rw [e]
    exact hcomb la v hv
  obtain ⟨hnu, hnu'⟩ := GlobalTheory.numerical_h_one_of_weighted_bound D T h j hj large₂ wL nus hH1
  have hg0 : 1 ≤ WeightAlgebra.g0 D := by
    have := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.dimPos_fr D).2
    unfold WeightAlgebra.g0
    omega
  let d := dataOf hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
  have hwe : ∀ k, d.w (eN.symm k) = valC hG (wtA wL) wL.n (G.w k).1 := fun k => by
    show valC hG (wtA wL) wL.n (G.w (eN (eN.symm k))).1 = _
    rw [Equiv.apply_symm_apply]
  have ha1 : A1Bigness d := GlobalTheory.BigRec.independent_differentials_ratios_cusp_forms_trdeg D T h j hj hG ka wL wF G d eN.symm rfl hwe (fun Z => valC_ne_zero (hwb Z))
    (fun Z => ⟨k0 Z, hk0 Z, hk0' Z⟩)
  obtain ⟨eD, heD⟩ := GlobalTheory.SectionBasis.chosenForms_restrict_basis_functionField D T h j hj hG ka wL wF G S g0 (Classical.arbitrary _) d eN.symm rfl hwe
    (fun Z => valC_ne_zero (hwb Z)) hH (hIB _)
  have ha4 : A4Selection d eD := heD eD (fun _ => rfl) rfl
  have hdel : d.del = G.del := by simpa using Fintype.card_congr eD
  have hdel1 : 1 ≤ d.del := by
    obtain ⟨e, -, -, h3⟩ := ha4
    obtain ⟨q, hq, p, hp⟩ := h3 (fun _ => 1)
    obtain ⟨Z⟩ := hne
    by_contra h0
    have : IsEmpty (Fin d.del) := ⟨fun i => by have := i.2; omega⟩
    have h4 := hp Z
    rw [mul_one, Finset.univ_eq_empty, Finset.sum_empty] at h4
    exact hq Z h4
  have hn96 : d.n96 = 8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊) := by
    rw [← hdel, ← hN]; rfl
  have hn1 : 1 ≤ d.n96 := by
    have : 0 < d.del := hdel1
    show 0 < 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊)
    positivity
  rw [← hn96] at hLAM hLC
  obtain ⟨-, -, hDF', hST⟩ := GlobalTheory.Reg.kap_divFin_stLoc_dataOf _ _ _ _ (T.Q.Xo j) T.Q.c hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    (by omega) hdim hwb ha1
  have hbdd : LawBdd d := GlobalTheory.Reg.LawBddPf.lawBdd_dataOf _ _ _ _ (T.Q.Xo j) T.Q.c hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    hcx (fun k => ⟨hse _ _, (hsup _ _).1⟩) (fun k => ⟨hse _ _, (hsup _ _).1⟩) ⟨hse _ G.et, (hsup _ G.et).1⟩
    ⟨hse _ _, (hsup _ _).1⟩ ⟨hse _ _, (hsup _ _).1⟩ huet hu1 hu2
  have ha2 : A2RegularityOrders d := by
    refine ⟨fun Z v hA x hx hx0 => ?_, fun Z v hA x hx hx0 => ?_, fun Z v hA => ?_, fun Z v hA => ?_,
      fun Z v hA => ?_⟩
    · obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG hG hx
      exact ord_nonneg_of_regP hreg hT hTQ (dom_wtA wL)
        (mem_of_mem_span_int _ (Set.range_subset_iff.2 fun k => hcu _ (G.w (eN k))) hF)
        (intAlg_span (Set.forall_mem_range.2 fun k => hin _ _ (hTW.2.1 (eN k))) hF) hA (evC_ne_zero_of_valC hx0)
    · obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG hG hx
      exact ord_nonneg_of_regP hreg hT hTQ (dom_wtA wF)
        (mem_of_mem_span_int _ (Set.range_subset_iff.2 fun k => hcu _ (G.th' k)) hF)
        (intAlg_span (Set.forall_mem_range.2 fun k => hin _ _ (hthM k)) hF) hA (evC_ne_zero_of_valC hx0)
    · have h0 := ord_nonneg_of_regP hreg hT hTQ (dom_wtA (wEt D j G.iet)) (hcu _ G.et) (hin _ _ hetM) hA (hetZ Z)
      rw [huet] at h0
      exact h0
    · have h0 := ord_nonneg_of_regP hreg hT hTQ (dom_wtA w1) (hcu _ t1) (hin _ _ ht1M) hA (h1Z Z)
      rw [hu1] at h0
      exact h0
    · have h0 := ord_nonneg_of_regP hreg hT hTQ (dom_wtA w2) (hcu _ t2) (hin _ _ ht2M) hA (h2Z Z)
      rw [hu2] at h0
      exact h0
  have ha3 : LawA3' d := lawA3'_dataOf hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 hDF' (hFr d hDF')
  have ha13 : A13Measurable d := lawA13_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    (nrmContOff_of hG fn yP _ _ _ _ _ hST
      (GlobalTheory.T.frameNorms_continuous_along_embedding_families _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r _ hU (xiR D) fn hx hpin hG yP hyP).1 hfn htr hfg hwb)
  have hnum : NumOK d := by
    have hg0' : (1 : ℝ) ≤ WeightAlgebra.g0 D := by exact_mod_cast hg0
    refine ⟨hD3, hi, hg0, hc0, ?_, hcg, ?_, ?_, ?_, hnK, hrd, p1, le_rfl, le_rfl, p2, le_rfl, p3, p4, p5, p6, p7,
      p8, p9⟩
    · show c ≤ 1
      nlinarith
    · show 1 ≤ wsize (wtZ (wtA wL) wL.n)
      rw [hsL]; exact hsz
    · show (WeightAlgebra.DF wL : ℝ) ≤ wsize (wtZ (wtA wL) wL.n)
      rw [hsL]; exact hDF
    · show Real.log (N + 1 : ℕ) + 1 / 2 ≤ Prw * (wsize (wtZ (wtA wL) wL.n) - 1)
      rw [hsL, hN]; exact hrw
  have iH1 : d.FinitePlaceHyp := height_H1_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    (T.U j) hreg (dom_wtA wL) (dom_wtA (wEt D j G.iet)) (fun k => hcu _ _) (hcu _ G.et) hnz hetZ hwb huet hc0
    (by rw [hnu']; exact hcomb') _ _ _ hTOn (by
      show NumericalH1Condition _ _ PN' (wsize (wtZ (wtA wL) wL.n))
      rw [hsL]
      exact ⟨hnu.1, hnu.2.1, hnu.2.2.trans (mul_le_mul_of_nonneg_right hPN (by linarith))⟩)
  have iF1d : d.TrivialPlaceHyp := height_F1_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    (T.U j) hreg hTQZ (dom_wtA wL) (dom_wtA (wEt D j G.iet)) (fun k => hcu _ _) (hcu _ G.et) hnz hetZ huet hc0
    nus hcomb'
  have hkaZ : wtZ (wtA (wsmul d.n96 wL)) (wsmul d.n96 wL).n = d.n96 • wtZ (wtA wL) wL.n :=
    (GlobalTheory.LowerBoundCompare.eq_wsmul_iff h.toLawsCore _ wL _).2 rfl
  have iLAM : d.HtLAM := htLAM_of h.toLawsCore j hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    large₂ CL AL (wsmul d.n96 wL) hgt hkaZ hLAM
    (prodInLat_of_wtZ h.toLawsCore j hj wR wL _ _ (fun k => ⟨G.w (eN k), hTW.2.1 _, rfl⟩) hn1 hkaZ)
    (Generic.supPTGe_of_fnPin D T.toCore h.toLawsCore j hj fn hpin hG yP hyP _) (by
      show LamConst j large₂ CL AL _ PP0' d.n96 (wsize (wtZ (wtA wL) wL.n))
      rw [hsL]; exact hLC)
  have hlog := fun (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w) (σ : T.Q.c.F →+* ℂ) =>
    log_iSup_le h j hG hV hfn hPT hcx F (hsup w F) σ
  have iSup' : d.HtSup := by
    refine ⟨?_, fun k => ?_, ?_, ?_⟩
    · show _ ≤ Gc * wsize (wtZ (wtA wL) wL.n)
      rw [hsL]
      refine (meanK_mono' fun σ => ?_).trans hTW.2.2.2.2
      exact ciSup_le fun k => (hlog _ (G.w (eN k)) σ).trans (hTW.2.2.2.1 σ _)
    · show _ ≤ Gc * wsize (wtZ (wtA wF) wF.n)
      rw [hsF]
      exact (meanK_mono' fun σ => hlog _ (G.th' k) σ).trans (hTT k).2
    · show _ ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wsize (wtZ (wtA wL) wL.n)
      rw [hsL]
      refine meanK_le_const fun σ => le_trans ?_ (ht1S σ)
      have h1 := hlog _ t1 σ
      rw [hu1] at h1
      exact h1
    · show _ ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wsize (wtZ (wtA wL) wL.n)
      rw [hsL]
      refine meanK_le_const fun σ => le_trans ?_ (ht2S σ)
      have h1 := hlog _ t2 σ
      rw [hu2] at h1
      exact h1
  have iet : d.HeightIntegralEstimateTrivialPlace := by
    refine htI2et_of_pt d fun σ => le_trans ?_ (hetS σ)
    have h1 := hlog (wEt D j G.iet) G.et σ
    rw [huet] at h1
    exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
  have ibe : d.HeightIntegralBoundEstimate := by
    have h3 := Generic.nrmTieU_of_fnPin D T.toCore h.toLawsCore j hj fn hpin hG yP hyP
    refine htI2be_of hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 (T.U j) (xiR D) th hi hc0 hfn hetZ huet
      (h3 N wR _ _ _ (dom_wtA wL) (dom_wtA (wEt D j G.iet)) (fun k => hse _ _) (hse _ G.et)) ?_
      (fun σ hσ k x hx => harch σ hσ k x hx)
    intro σ hσ k x hx
    have e : ∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (wR k') k x ^ 2 =
        ∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2 :=
      eN.sum_comp (fun k' => recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)
    have h1 := hI2 σ hσ k x hx
    rw [← e] at h1
    exact h1
  let hd : d.AxH (fun Z => AG Z) := axHOf hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    hne hfg htr hac hwb hetZ h1Z h2Z huet hu1 hu2 hfn hconj hbdd ha1 ha2 ha3 eD ha4 hnum ha13
  have hsel : hd.sel = eD := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hnum
    rfl
  have hs := d.genericSection_of_axioms hd
  have hcon := d.heights hd hs iH1 iF1d iLAM iSup' iet ibe
  refine Formalism.MainNotions.Gaps.HeightData.heights_of_htConcl G _ Gc PH Prw Pet
    (htConcl_toHtData_of (B := recB h.toLawsCore) d hd hs G _ Gc PH Prw Pet rfl hdel rfl rfl hsL rfl hPH.symm rfl rfl
      ?_ ?_ ?_ hcon)
  · rw [← eD.sum_comp]
    refine Finset.sum_le_sum fun k _ => ?_
    show meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) ≤ _
    rw [hsel]
    exact meanK_mono' fun σ => hlog _ (G.th' (eD k)) σ
  · exact GlobalTheory.T.lengths_at_primes_le_functionField_data_of_curve D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie δ hT d hd hs eN rfl
      (fun _ _ => rfl) rfl rfl (fun _ => rfl) eD (fun k => by rw [hsel]; rfl) Gc PH Prw Pet
  · exact GlobalTheory.T.orders_auxiliary_form_at_primes_eq_functionField D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie hjm δ hT d hd hs eN rfl
      (fun _ _ => rfl) rfl rfl (fun _ => rfl) rfl huet.symm Gc PH Prw Pet

end GlobalTheory.HeightTop
