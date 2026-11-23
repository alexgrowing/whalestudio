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
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LawBddDataOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeightZZeroEqTwoSmulSubSelf
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExtendByZeroConstMul
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCBaseValAtCx
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapDivFinStLocDataOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NotGoodConj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwise
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupBddAndSupREqSupN
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsReadingDensKNrmTieU
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RamOverZRealPos
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndependentDifferentialsRatiosOfTrdegValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrdTiesOfPins
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LengthsAtPrimesLeFunctionFieldDataOfCurveStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ChosenFormsRestrictBasisFunctionField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeightDefinite

section Weights

variable {D : D7} {j : ℕ}

theorem wtZ_wsmul (k : ℕ) (w : WeightFamilies.Wt D j) : wtZ (wtA (wsmul k w)) (wsmul k w).n = k • wtZ (wtA w) w.n := by
  rw [GlobalTheory.Reg.wtA_wsmul_eq]
  ext <;> simp [wtZ, wsmul]

theorem weightSumVector_secondGeneratorWeight_definite {wL wF w2 : WeightFamilies.Wt D j} (hG : IsG2 wL wF w2) :
    wtZ (wtA w2) w2.n = (WeightFamilies.dimY D j + 4 : ℕ) • wtZ (wtA wL) wL.n - wtZ (wtA wF) wF.n := by
  have e : wadd w2 wF = wsmul (WeightFamilies.dimY D j + 4) wL := by
    apply deg_inj
    simp only [deg, wadd, wsmul, Prod.mk.injEq]
    exact ⟨funext fun τ => funext fun i => hG.2.1 τ i, funext fun τ => funext fun i => hG.2.2 τ i, hG.1⟩
  rw [eq_sub_iff_add_eq, ← wtZ_add, ← wtA_wadd, ← n_wadd, e, wtZ_wsmul]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj {Q : Par D} (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h5 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := Q.H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(Q.H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < Q.H.d := by exact_mod_cast Q.H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem wtA_tau {Q : Par D} (hp : Q.PinHost) (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj hp, this]
  · simp

theorem wtA_conj_tau {Q : Par D} (hp : Q.PinHost) (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  have h0 : ∀ τ : D.host.E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => by
    ext x
    simp [conjEmb]
  have h1 : ∀ t', conjEmb (DV.tauEmb D t) ≠ DV.tauEmb D t' := fun t' h => tauEmb_ne_conj hp t' t h.symm
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [h1]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h =>
      ht' (tauEmb_inj (by rw [← h0 (DV.tauEmb D t'), ← h, h0]))
    simp [h1, this]
  · simp

theorem eq_of_wtZ_eq {Q : Par D} (hp : Q.PinHost) {w w' : WeightFamilies.Wt D j}
    (e : wtZ (wtA w) w.n = wtZ (wtA w') w'.n) : w = w' := by
  have e1 : ∀ x, wtA w x = wtA w' x := fun x => by
    have := congrFun (congrArg Prod.fst e) x
    simpa [wtZ] using this
  have e2 : w.n = w'.n := by
    have := congrArg Prod.snd e
    simpa [wtZ] using this
  apply deg_inj
  simp only [deg, Prod.mk.injEq]
  refine ⟨funext fun t => funext fun i => ?_, funext fun t => funext fun i => ?_, e2⟩
  · have := e1 (DV.tauEmb D t, i)
    rw [wtA_tau hp, wtA_tau hp] at this
    simpa [ext0, i.isLt] using this
  · have := e1 (conjEmb (DV.tauEmb D t), i)
    rw [wtA_conj_tau hp, wtA_conj_tau hp] at this
    simpa [ext0, i.isLt] using this

theorem exists_wsize {Q : Par D} (hp : Q.PinHost) (w w' : WeightFamilies.Wt D j) :
    ∃ s : WTZ D.host.E → ℝ, s (wtZ (wtA w) w.n) = w.size ∧ s (wtZ (wtA w') w'.n) = w'.size := by
  classical
  refine ⟨fun u => if u = wtZ (wtA w) w.n then w.size else w'.size, if_pos rfl, ?_⟩
  by_cases e : wtZ (wtA w') w'.n = wtZ (wtA w) w.n
  · exact (if_pos e).trans (by rw [eq_of_wtZ_eq hp e])
  · exact if_neg e

end Weights

theorem ev_ne_zero_of_nonZeroComp {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {ι : Type}
    (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (w : WeightFamilies.Wt D j) (g : B.Cusp j w), (∀ Z, gF Z (X.inc w g) = 0) → g = 0)
    {u : WeightFamilies.Wt D j} {F : B.Cusp j u} (hF : X.NonZeroComp u F) (Z : ι) {w : WeightFamilies.Wt D j} (g : B.Cusp j w)
    (hg : gF Z (X.inc w g) ≠ 0) (hg' : ∀ Z', Z' ≠ Z → gF Z' (X.inc w g) = 0) : gF Z (X.inc u F) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul u w F g
  have hH0 : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [hg' Z' hZ, mul_zero]
  rw [hH0, map_zero] at hH
  have := hF w g hH
  rw [this, map_zero, map_zero] at hg
  exact hg rfl

section Forms

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

theorem nzAt_of_nonZeroComp (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (hV : GenValInjSt h j hG)
    (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F) : NZAt hG (F : T.R j) := by
  intro Z
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, e1, e2⟩ := hC Z wL (G.w k)
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun w g hg => hV w g fun Z => (formsEvR_inc h j hj hG hT Z w g).symm.trans (hg Z)) hF Z g
    (fun h0 => hk (e1.symm.trans ((formsEvR_inc h j hj hG hT Z wL g).symm.trans h0)))
    (fun Z' hZ' => (formsEvR_inc h j hj hG hT Z' wL g).trans (e2 Z' hZ'))
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z u F).trans h0)

theorem exists_comb [Fintype (Comp (T.Q.Xo j) T.Q.c)] {w : WeightFamilies.Wt D j} {n : ℕ}
    (f : Fin n → (recB h.toLawsCore).Cusp j w) (hf : ∀ k, f k ∈ (recB h.toLawsCore).Mlat j w)
    (hne : ∀ Z, ∃ k, evC hG Z (f k).1 ≠ 0) :
    ∃ F : (recB h.toLawsCore).Cusp j w, F ∈ (recB h.toLawsCore).Mlat j w ∧ NZAt hG F.1 := by
  have : ∀ Z : Comp (T.Q.Xo j) T.Q.c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap T.Q.c.F (Om Z)).injective
  obtain ⟨m, hm⟩ := exists_nat_comb (Ω := fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z) (fun Z k => evC hG Z (f k).1) hne
  refine ⟨∑ k, m k • f k, Submodule.sum_mem _ fun k _ => nsmul_mem (hf k) _, fun Z h0 => hm Z ?_⟩
  let φ : (recB h.toLawsCore).Cusp j w →+ Om Z :=
    { toFun := fun F => evC hG Z F.1
      map_zero' := evC_zero hG Z
      map_add' := fun F F' => evC_add hG Z F.1 F'.1 }
  have h1 : φ (∑ k, m k • f k) = 0 := h0
  rw [map_sum] at h1
  simp only [map_nsmul, nsmul_eq_mul] at h1
  exact h1

end Forms

theorem one_le_del {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)] (hne : CompNe Xo c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
    (sel : Fin d.del → Fin d.np) (ha : A4Selection d sel) : 1 ≤ d.del := by
  obtain ⟨e, -, -, h3⟩ := ha
  obtain ⟨q, hq, p, hp⟩ := h3 fun _ => 1
  obtain ⟨Z⟩ := hne
  by_contra h0
  have : IsEmpty (Fin d.del) := ⟨fun k => by have := k.2; omega⟩
  have h1 := hp Z
  rw [Finset.univ_eq_empty, Finset.sum_empty, mul_one] at h1
  exact hq Z h1

section Orders

open ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
  (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)

theorem ord_nonneg_of_regP {rU : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU} (hreg : regular₂ Xo c U)
    (hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdom : Dom a n) {F : Rul Xo c} (hFC : F ∈ cusp Xo c U a n) (hF : IntAlg F)
    {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)} (hd : IsNormDiscrete v)
    (hv : (∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) (hne : evC h Z F ≠ 0) :
    0 ≤ ordC (δ Z v) v (wtZ a n) (valC h a n F Z) := by
  have hFs := cusp_le_sec Xo c U a n hFC
  have hR := hreg.1.1 ⟨(a, n), hdom⟩ ⟨F, hFC⟩ fun la y => hF la y.1 y.2
  have key : (0 : EReal) ≤ (((ordC (δ Z v) v (wtZ a n) (valC h a n F Z) : ℤ) : ℝ) : EReal) := by
    rcases hv with ⟨la, ho⟩ | ht
    · obtain ⟨y, hy⟩ := hT Z v la hd ho
      rw [hy a n F hFs hne]
      exact mul_nonneg (by exact_mod_cast ramIdx_nonneg ho) (hR.1 la ⟨vAtV y, y, rfl⟩)
    · obtain ⟨q, hq⟩ := hTQ Z v hd ht
      rw [hq a n F hFs hne]
      have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
        refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
        obtain ⟨u, hu⟩ := q.triv a ha
        rw [← hu]
        exact extVal_unit_zero q.T u
      exact hR.2 ⟨_, hqT⟩
  exact_mod_cast key

variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL uF uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (etR ta2R : Rul Xo c)
    (nu : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (wsize : WTZ E → ℝ) (DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO : ℝ)

theorem secondHeightLaw_of_regularUniformisation {rU : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU} (hreg : regular₂ Xo c U)
    (hgt : GenFromTest Xo c h)
    (hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)
    (hdL : Dom uL.1 uL.2) (hdF : Dom uF.1 uF.2) (hd2 : Dom uta2.1 uta2.2)
    (hwC : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2) (hwI : ∀ k, IntAlg (wR k))
    (hpC : ∀ k, thpR k ∈ cusp Xo c U uF.1 uF.2) (hpI : ∀ k, IntAlg (thpR k))
    (heC : etR ∈ cusp Xo c U uL.1 uL.2) (heI : IntAlg etR) (heN : NZAt h etR)
    (h2C : ta2R ∈ cusp Xo c U uta2.1 uta2.2) (h2I : IntAlg ta2R) (h2N : NZAt h ta2R)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2) :
    A2RegularityOrders (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO) := by
  have cases' : ∀ {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)},
      (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).admitted Z v →
      IsNormDiscrete v ∧ ((∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) := by
    intro Z v hA
    obtain ⟨hd, hc⟩ := hA
    exact ⟨hd, hc.imp (fun h' => let ⟨la, ho, _⟩ := h'; ⟨la, ho⟩) (fun h' => h'.1)⟩
  refine ⟨fun Z v hA x hx hx0 => ?_, fun Z v hA x hx hx0 => ?_, fun Z v hA => ?_, fun Z v hA => ?_,
    fun Z v hA => ?_⟩
  · obtain ⟨hd, hc⟩ := cases' hA
    obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG h hx
    exact ord_nonneg_of_regP h δ hreg hT hTQ hdL (mem_of_mem_span_int _ (Set.range_subset_iff.2 hwC) hF)
      (intAlg_span (Set.forall_mem_range.2 hwI) hF) hd hc (evC_ne_zero_of_valC hx0)
  · obtain ⟨hd, hc⟩ := cases' hA
    obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG h hx
    exact ord_nonneg_of_regP h δ hreg hT hTQ hdF (mem_of_mem_span_int _ (Set.range_subset_iff.2 hpC) hF)
      (intAlg_span (Set.forall_mem_range.2 hpI) hF) hd hc (evC_ne_zero_of_valC hx0)
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of_regP h δ hreg hT hTQ hdL heC heI hd hc (heN Z)
    show 0 ≤ ordC (δ Z v) v ((1 * 1 : ℕ) • wtZ uL.1 uL.2) (valC h uL.1 uL.2 etR Z)
    rw [← wt_et]
    exact h0
  · show 0 ≤ ordC (δ Z v) v ((2 : ℕ) • (wtZ uL.1 uL.2 - wtZ uL.1 uL.2)) (valC h 0 0 1 Z)
    have hz : frW (δ Z v) (0 : WTZ E) = 0 := by
      simp only [frW]
      exact Finset.sum_eq_zero fun i _ => by cases i <;> simp [exZ]
    rw [sub_self, smul_zero]
    simp only [valC, wtZ_zero, evC_one hgt, ordC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, hz,
      AddValuation.map_one, add_zero]
    exact le_rfl
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of_regP h δ hreg hT hTQ hd2 h2C h2I hd hc (h2N Z)
    rw [huta2] at h0
    exact h0

theorem exists_htI2et : ∃ Pet : ℝ, 1 ≤ Pet ∧
    (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HeightIntegralEstimateTrivialPlace :=
  ⟨max 1 _, le_max_left _ _, le_max_right 1 (meanK (fun σ => Real.log
      (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ),
        nrmC fn (yP p.1) ((1 * 1 : ℕ) • wtZ uL.1 uL.2) (valC h uL.1 uL.2 etR p.1) p.2)) / ((1 : ℕ) : ℝ))⟩

end Orders

theorem heights_definite :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j = D.R.m → FnAlgClosed (T.Q.Xo j) T.Q.c → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → (∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ)) → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hV hC hB y hw hcur htie hjm hac hD3 _ hbas large₂ Gc PH Prw Pet PN' PP0' PI4'
    tableLineDegreeFive tableLineDegreeTwo POb CL AL nus w2 t2 hTW hTT hthM hG2 ht2M ht2N ht2S hH1w hPN hlam hlc hL1 hDF hrw hnK hrd
    gPN gPP0 gGc gPI4 _ gP14 gP16 gPrw gPO hPH hval harch
  classical
  have hgt : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  obtain ⟨hkfg, -, htr, hne, δ, hTQ, hTQZ, hTO, hT, hFr⟩ := Ties.ordTies_of_pins D T.Q h.pins j hj hG
  have hreg := h.reg j hj
  obtain ⟨-, -, -, hx, -, -, hrk⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, -, hdim⟩ := hrk j hj
  have hfg := fnFG_of (T.Q.Xo j) T.Q.c hkfg
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ =>
    (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))
  obtain ⟨fn, hpin, hfn⟩ := GlobalTheory.FrameNorm.Existence.exists_pinned _ _ _ _ _ _ _ _ hU _ hx
  obtain ⟨yP, hyP, hcx, -⟩ := GlobalTheory.Reg.exists_cBase_valAtCx _ _ _ _ (T.Q.Xo j) T.Q.c
    (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1 hG
  have hconj := (GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm _ _ _ _ _ _ _ _ hU _ fn hx hpin hG yP hyP).1
  obtain ⟨-, hsup, -⟩ := GlobalTheory.FrameNorm.RecSup.supBdd_and_supR_eq_supN D T h j hj fn hpin
  obtain ⟨-, -, -, hnt⟩ := Generic.exists_reading_densK_nrmTieU D T.toCore h.toLawsCore j hj fn hpin
    hG yP hyP
  have hcusp : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := fun w F => cutR_le T.C j w F.2
  have hsec : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := fun w F => cusp_le_sec _ _ _ _ _ (hcusp w F)
  have hint : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), F ∈ (recB h.toLawsCore).Mlat j w →
      IntAlg F.1 := fun _ _ hF => hF
  have hNZ : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZSome hG F.1 ∨ F.1 = 0 := by
    intro w F
    by_cases h0 : NZSome hG F.1
    · exact Or.inl h0
    · right
      rw [hV w F fun Z => by_contra fun hZ => h0 ⟨Z, hZ⟩]
      rfl
  have hBig := hH.2.1
  have hk0 : ∀ Z, ∃ k, evC hG Z (G.w k).1 ≠ 0 := fun Z => (hBig.2 Z).imp fun _ hk => hk.1
  obtain ⟨N, hN⟩ : ∃ N, G.N = N + 1 := by
    obtain ⟨Z⟩ := hne
    obtain ⟨k, -⟩ := hk0 Z
    exact ⟨G.N - 1, by have := k.2; omega⟩
  obtain ⟨e⟩ : Nonempty (Fin (N + 1) ≃ Fin G.N) := ⟨finCongr hN.symm⟩
  obtain ⟨jc, hwb⟩ : ∃ jc : Comp (T.Q.Xo j) T.Q.c → Fin (N + 1), ∀ Z, evC hG Z (G.w (e (jc Z))).1 ≠ 0 := by
    choose k hk using hk0
    exact ⟨fun Z => e.symm (k Z), fun Z => by rw [e.apply_symm_apply]; exact hk Z⟩
  obtain ⟨et, hetM, hetN⟩ := exists_comb h j hG G.w hTW.2.1 hk0
  have ht2Z : NZAt hG t2.1 := nzAt_of_nonZeroComp h j hj hG hgt hV hC G hBig t2 ht2N
  obtain ⟨ws, hwL, hwF⟩ := exists_wsize h.pins.1 wL wF
  obtain ⟨hnu, hnus⟩ := GlobalTheory.numerical_h_one_of_weighted_bound D T h j hj large₂ wL nus hH1w
  have huta2 := weightSumVector_secondGeneratorWeight_definite hG2
  obtain ⟨Pet', gPet, hI2et⟩ := exists_htI2et hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' tableLineDegreeFive tableLineDegreeTwo Prw POb
  have hnz : NoCommonZero (T.Q.Xo j) T.Q.c fun k => (G.w (e k)).1 := by
    intro k _ _ _ y
    obtain ⟨i, hi⟩ := hBig.1 k y
    exact ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩
  have hcomb : CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w (e k)).1) et.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (0 / (2 * ((1 : ℕ) : ℝ))) := by
    intro la v hv
    refine ⟨hint _ _ hetM la v hv, fun _ => ?_⟩
    rw [zero_div, EReal.coe_zero, zero_mul, add_zero, hnus, e.iInf_comp (g := fun k => v (G.w k).1)]
    exact hval la v hv
  have hpl : Nonempty (HeightOneSpectrum (𝓞 T.Q.c.F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 T.Q.c.F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)⟩⟩
  have hwd : ∀ k, (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).w (e.symm k) = valC hG (wtA wL) wL.n (G.w k).1 := fun k => by
    show valC hG (wtA wL) wL.n (G.w (e (e.symm k))).1 = _
    rw [e.apply_symm_apply]
  have hwd0 : ∀ Z, (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).w ((dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).jc Z) Z ≠ 0 := fun Z => valC_ne_zero (hwb Z)
  have ha1 : A1Bigness (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) :=
    GlobalTheory.BigRec.independent_differentials_ratios_cusp_forms_trdeg D T h j hj hG ka wL wF G (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) e.symm rfl hwd hwd0 hBig.2
  obtain ⟨la0⟩ := id hpl
  obtain ⟨eδ, ha4'⟩ := Basis.chosenForms_restrict_basis_functionField D T h j hj hG ka wL wF G S g0 la0 (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) e.symm rfl hwd hwd0 hH (hbas la0)
  have ha4 : A4Selection (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) eδ := ha4' eδ (fun _ => rfl) rfl
  have hdel : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).del = G.del := Fin.equiv_iff_eq.1 ⟨eδ⟩
  obtain ⟨-, -, hdiv, hst⟩ := GlobalTheory.Reg.kap_divFin_stLoc_dataOf _ _ _ _ _ _ hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 (by omega) hdim.symm hwb ha1
  have ha3 : LawA3' (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) := lawA3'_of _ δ (fun _ _ => rfl) hdiv (hFr _ hdiv)
  have ha13 : A13Measurable (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) := lawA13_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    ((GlobalTheory.FrameNorm.nrmAlong_of_fnPin _ _ _ _ _ _ _ _ hU _ fn hx hpin hG yP hyP).2 _ _ _ _ _ hst htr hwb)
  have hbdd := lawBdd_dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb hcx huta2 (fun k => hsec _ _) (fun k => (hsup _ _).1) (fun k => hsec _ _)
    (fun k => (hsup _ _).1) (hsec _ _) (hsup _ _).1 (hsec _ _) (hsup _ _).1
  have ha2 := secondHeightLaw_of_regularUniformisation hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb hreg hgt hT hTQ (dom_wtA wL) (dom_wtA wF) (dom_wtA w2)
    (fun k => hcusp _ _) (fun k => hint _ _ (hTW.2.1 _)) (fun k => hcusp _ _) (fun k => hint _ _ (hthM _))
    (hcusp _ _) (hint _ _ hetM) hetN (hcusp _ _) (hint _ _ ht2M) ht2Z huta2
  have hnum : NumOK (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) := by
    refine ⟨hD3, le_rfl, le_rfl, le_rfl, zero_le_one, ?_, hL1.trans hwL.ge, hDF.trans hwL.ge, ?_, hnK, hrd,
      gPN, le_rfl, le_rfl, gPP0, le_rfl, gGc, gPI4, gPet, gP14, gP16, gPrw, gPO⟩
    · show (0 : ℝ) * _ ≤ 1 / 2
      norm_num
    · show Real.log (N + 1 : ℕ) + 1 / 2 ≤ Prw * (ws (wtZ (wtA wL) wL.n) - 1)
      rw [hwL, ← hN]
      exact hrw
  have hnu' : NumericalH1Condition T.Q.c (fun la => nus la / (ramOverZ la : ℝ)) PN' (ws (wtZ (wtA wL) wL.n)) := by
    refine ⟨hnu.1, hnu.2.1, hnu.2.2.trans ?_⟩
    rw [hwL]
    exact mul_le_mul_of_nonneg_right hPN (by linarith)
  have hH1 : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).FinitePlaceHyp := height_H1_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 (T.U j) hreg (dom_wtA wL) (dom_wtA wL)
    (fun k => hcusp _ _) (hcusp _ _) hnz hetN hwb (wt_et _) le_rfl hcomb _ _ _ hTO hnu'
  have hF1d : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).TrivialPlaceHyp := height_F1_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 (T.U j) hreg hTQZ (dom_wtA wL) (dom_wtA wL)
    (fun k => hcusp _ _) (hcusp _ _) hnz hetN (wt_et _) le_rfl _ hcomb
  have hn96 : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).n96 = (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) := by
    show 8 * ((WeightFamilies.dimY D j + 2) * (N + 1)) ^ 2 * (WeightFamilies.dimY D j + 1) * (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).del * (1 + ⌈POb⌉₊) = _
    rw [hdel, ← hN]
  have hn1 : 1 ≤ (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) := by
    have h1 := one_le_del hne _ _ ha4
    rw [hdel] at h1
    have h2 : 0 < G.N := by omega
    have h3 : 0 < G.del := h1
    exact Nat.succ_le_of_lt (by positivity)
  have hLAM : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).HtLAM := by
    refine htLAM_of h.toLawsCore j hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) hgt ?_ hlam ?_
      (Generic.supPTGe_of_fnPin D T.toCore h.toLawsCore j hj fn hpin hG yP hyP _) ?_
    · exact (wtZ_wsmul _ _).trans (congrArg (fun n : ℕ => n • wtZ (wtA wL) wL.n) hn96.symm)
    · have h1 := prodInLat_of_wtZ h.toLawsCore j hj (fun k => (G.w (e k)).1) wL _ _
        (fun k => ⟨G.w (e k), hTW.2.1 _, rfl⟩) hn1 (wtZ_wsmul _ _)
      exact Eq.mp (congrArg (ProdInLat h.toLawsCore j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) fun k => (G.w (e k)).1) hn96.symm) h1
    · exact Eq.mp (congrArg₂ (LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0') hn96.symm hwL.symm) hlc
  have hSup := htSup_dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb hgt hfn hfg hcx huta2
    (fun k => hsec _ _) (fun k => (hsup _ _).1) (fun k => hNZ _ _)
    (fun k => hsec _ _) (fun k => (hsup _ _).1) (fun k => hNZ _ _) (hsec _ _) (hsup _ _).1 (hNZ _ _) G.mx
    (fun σ k => ((congrArg Real.log ((hsup _ _).2 σ)).le).trans (hTW.2.2.2.1 σ _))
    (by rw [hwL]; exact hTW.2.2.2.2)
    (fun k => by
      rw [hwF]
      simp only [(hsup wF (G.th' k)).2]
      exact (hTT k).2)
    (by rw [hwL]; positivity)
    (fun σ => by
      rw [hwL]
      exact ((congrArg Real.log ((hsup _ _).2 σ)).le).trans (ht2S σ))
  have hI2be := htI2be_dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb (T.U j) (xiR D)
    (hnt N (fun k => (G.w (e k)).1) (wtA wL, wL.n) et.1 (wtA wL, wL.n) (dom_wtA wL) (dom_wtA wL)
      (fun k => hsec _ _) (hsec _ _))
    (fun σ hσ k x hx => by
      rw [e.sum_comp fun k' => recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2]
      exact harch σ hσ k x hx)
  obtain ⟨hd, hs, hsel, hcon⟩ := exists_htConcl hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb hgt hne hfg htr hac hwb hetN ht2Z huta2 hfn hconj hbdd ha1 ha2
    ha3 eδ ha4 hnum ha13 hH1 hF1d hLAM hSup hI2et hI2be
  have hI := GlobalTheory.T.lengths_at_primes_le_functionField_data_of_curve D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie δ hT (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) hd hs e rfl
    (fun _ _ => rfl) rfl rfl (fun _ => rfl) eδ (fun k => by rw [hsel]; rfl) Gc PH Prw Pet
  refine heights_of_first (B := recB h.toLawsCore) (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) hd hs G _ Gc PH Prw Pet (by omega) rfl hdel hwL rfl
    hPH.symm rfl ?_ hI hcon
  rw [← eδ.sum_comp]
  refine Finset.sum_le_sum fun k _ => ?_
  show ReciprocityTheory.ChartRestriction.G.T0.meanK (fun σ => Real.log
      (⨆ p : (Σ Z : Comp (T.Q.Xo j) T.Q.c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) σ),
        nrmC fn (yP p.1) (wtZ (wtA wF) wF.n) (valC hG (wtA wF) wF.n (G.th' (hd.sel k)).1 p.1) p.2)) ≤ _
  rw [hsel]
  refine (meanK_mono' fun σ => log_sup_le hfn hfg hcx (hsec _ _) (hsup _ _).1 (hNZ _ _) σ).trans (le_of_eq ?_)
  simp only [(hsup wF (G.th' (eδ k))).2]
  rfl

end GlobalTheory.HeightDefinite
