import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnSeqShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellFrameOfSpans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChgFromBlocksEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.FlagCell
open GlobalTheory.MixDens (emb)
open GlobalTheory.MixDens.NormalCoord (emb_injective chg_submatrix_emb exists_upper_chg_eq_one sum_Iio)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.DualFlagBc

section Matrices

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  {N : ℕ} {K : E → Matrix (Fin N) (Fin N) ℂ} {z : E}

theorem extTrace_step_chg (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef)
    {T : Matrix (Fin N) (Fin N) ℂ} (hT : ∀ a c : Fin N, c < a → T a c = 0) (hu : IsUnit T.det) (i : Fin N) :
    extTrace (fun x => (chg T (K x)).submatrix (emb i) (emb i)) z =
      extTrace (fun x => (K x).submatrix (emb i) (emb i)) z := by
  simp only [chg_submatrix_emb hT]
  refine extTrace_chg (A := fun _ => T.submatrix (emb i) (emb i)) (h.submatrix _ _)
    (hp.mono fun x hx => hx.submatrix (emb_injective i)) (mContDiffAt_const _) ?_
    (fun η => mdbar_const _ _ _) (.of_forall fun _ => ?_)
  · have h₁ := (posDef_chg ((isUnit_iff_isUnit_det _).2 hu)
      (PosDef.one (n := Fin N) (R := ℂ))).submatrix (emb_injective i)
    have h₂ := h₁.det_pos.ne'
    rw [chg_submatrix_emb hT, chg, det_mul, det_mul, det_transpose] at h₂
    exact (left_ne_zero_of_mul (left_ne_zero_of_mul h₂)).isUnit
  · ext a b
    exact hT _ _ b.isLt

theorem sum_extTrace_of_eq_one (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (h1 : K z = 1) (ξ η : E) :
    ∑ i, extTrace (fun x => (K x).submatrix (emb i) (emb i)) z ξ η =
      kappa * ∑ i, ∑ a, if a < i then mdel K z ξ a i * star (mdel K z η a i) else 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [extTrace_eq_sum_of_eq_one (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix (emb_injective i))
    (by rw [h1]; exact submatrix_one _ (emb_injective i)), ← Finset.sum_filter, Finset.filter_gt_eq_Iio, sum_Iio]
  simp only [Fin.sum_univ_one]
  rfl

def revDual (M : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := (dualGram M).submatrix Fin.rev Fin.rev

theorem sum_extTrace_revDual (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (ξ η : E) :
    ∑ i, extTrace (fun x => (revDual (K x)).submatrix (emb i) (emb i)) z ξ η =
      ∑ i, extTrace (fun x => (K x).submatrix (emb i) (emb i)) z ξ η := by
  obtain ⟨T, hT, h1⟩ := exists_upper_chg_eq_one hp.self_of_nhds
  have hu : IsUnit T.det := by
    have := congrArg Matrix.det h1
    rw [chg, det_mul, det_mul, det_transpose, det_one, mul_assoc] at this
    exact IsUnit.of_mul_eq_one _ this
  have hd {L : E → Matrix (Fin N) (Fin N) ℂ} (h : MContDiffAt 1 L z) (hp : ∀ᶠ x in 𝓝 z, (L x).PosDef) :
      MContDiffAt 1 (fun x => revDual (L x)) z ∧ ∀ᶠ x in 𝓝 z, (revDual (L x)).PosDef :=
    ⟨(h.inv hp.self_of_nhds.det_pos.ne'.isUnit).transpose.submatrix _ _,
      hp.mono fun x hx => (posDef_dualGram hx).submatrix Fin.rev_injective⟩
  have hL : MContDiffAt 1 (fun x => chg T (K x)) z := ((mContDiffAt_const _).mul h).mul (mContDiffAt_const _)
  have hLp : ∀ᶠ x in 𝓝 z, (chg T (K x)).PosDef :=
    hp.mono fun x hx => posDef_chg ((isUnit_iff_isUnit_det _).2 hu) hx
  have hTi : T⁻¹.BlockTriangular id :=
    have := invertibleOfIsUnitDet T hu
    blockTriangular_inv_of_blockTriangular fun a c h => hT a c h
  have e (M : Matrix (Fin N) (Fin N) ℂ) :
      revDual (chg T M) = chg (T⁻¹ᵀ.submatrix Fin.revPerm Fin.revPerm) (revDual M) := by
    rw [revDual, dualGram_chg (mul_nonsing_inv T hu)]
    exact (chg_submatrix _ _ Fin.revPerm Fin.revPerm).symm
  have e₁ (i : Fin N) := extTrace_step_chg h hp hT hu i
  have e₂ (i : Fin N) := extTrace_step_chg (hd h hp).1 (hd h hp).2
    (T := T⁻¹ᵀ.submatrix Fin.revPerm Fin.revPerm) (fun a c hc => hTi (Fin.rev_lt_rev.2 hc))
    (by rw [det_submatrix_equiv_self, det_transpose]; exact isUnit_nonsing_inv_det _ hu) i
  simp only [← e] at e₂
  simp only [← e₁, ← e₂]
  have h2 : revDual (chg T (K z)) = 1 := by
    rw [h1, revDual, dualGram, inv_one, transpose_one, submatrix_one _ Fin.rev_injective]
  have e₃ (ζ : E) (a b : Fin N) : mdel (fun x => revDual (chg T (K x))) z ζ a b =
      -mdel (fun x => chg T (K x)) z ζ b.rev a.rev := by
    have := mdel_inv hL (by rw [h1]; simp) ζ
    rw [h1, inv_one, Matrix.one_mul, Matrix.mul_one] at this
    exact congrFun (congrFun this b.rev) a.rev
  rw [sum_extTrace_of_eq_one (hd hL hLp).1 (hd hL hLp).2 h2, sum_extTrace_of_eq_one hL hLp h1, Finset.sum_comm,
    ← Equiv.sum_comp Fin.revPerm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [e₃, Fin.revPerm_apply, Fin.rev_rev, Fin.rev_lt_rev, star_neg, neg_mul_neg]

end Matrices

section Frames

variable {X : Scheme.{0}} {F : X.Modules} {N : ℕ} {fl : Vert.Flag F N} {U : X.Opens} {v : Fin N → Γ(F, U)}

theorem isFrame_of_spans (H : Spans fl U v) : IsFrame v := by
  obtain ⟨s, hs, es⟩ := H (Fin.last N)
  have := hs.map_iso (fl.ι (Fin.last N))
  rwa [funext es] at this

theorem exists_spans (fl : Vert.Flag F N) (x : X) : ∃ (U : X.Opens) (v : Fin N → Γ(F, U)), x ∈ U ∧ Spans fl U v := by
  choose U e hU he using fun k => fl.isVB_gr k x
  choose W hW hxW t ht using fun k => VBExt.exists_lifts (fl.π k) (e k) (hU k)
  have hV (k : Fin N) : Finset.univ.inf W ≤ W k := Finset.inf_le (Finset.mem_univ k)
  have ht' (k : Fin N) : IsFrame fun j : Fin 1 => (fl.π k).app _ (resM _ (hV k) (t k j)) := by
    simp only [app_resM, ht, resM_resM]
    exact (he k).res _
  refine ⟨Finset.univ.inf W, fun k => (fl.ι k.succ).app _ (resM _ (hV k) (t k 0)), by
    change x ∈ ((Finset.univ.inf W : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_finset_inf]; simpa using hxW, fun l => ?_⟩
  induction l using Fin.induction with
  | zero =>
    have z := VB.isVB_zero_iff.1 (fl.isVB 0)
    exact ⟨_, (VB.isFrame_freeFrame X (Fin 0)).map_iso ((VB.isVB_zero_iff.1
      (VB.isVB_freeModule_fin X 0)).iso z).hom |>.res le_top, fun j => j.elim0⟩
  | succ i ih =>
    obtain ⟨s, hs, es⟩ := ih
    have h := (VBExt.isFrame_sumElim (S := .mk (fl.step i) (Limits.cokernel.π _) (Limits.cokernel.condition _))
      { exact := ShortComplex.exact_cokernel _ } (t := fun j : Fin 1 => resM _ (hV i) (t i j)) hs (ht' i)).comp_equiv
      finSumFinEquiv.symm
    refine ⟨_, h, fun j => ?_⟩
    refine Fin.addCases (m := i) (n := 1) (fun j => ?_) (fun j => ?_) j
    · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
      refine Eq.trans ?_ (es j)
      rw [← fl.step_ι i]
      rfl
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      exact congrArg (fun z => (fl.ι i.succ).app _ (Sum.elim (fun j => (fl.step i).app _ (s j))
        (fun j : Fin 1 => resM _ (hV i) (t i j)) z)) (finSumFinEquiv_symm_apply_natAdd (m := i) (n := 1) 0)

theorem spans_dualFlag (H : Spans fl U v) (hv : IsFrame v) :
    Spans (DualFlag.dualFlag fl) U fun j => hv.coord j.rev := by
  intro l
  obtain ⟨s, hs, es⟩ := H l.rev
  have hex (V : X.Opens) := QCoh.exact_app_of_exact_of_mono (DualFlag.annSeq_shortExact fl l.rev).exact V
  have hz (j : Fin l) : (dualMap (fl.ι l.rev)).app U (hv.coord (Fin.castLE l.is_le j).rev) = 0 := by
    refine hs.dual_ext le_rfl fun a => ?_
    rw [dualApp_dualMap, app_resM, es, hv.dualApp_coord_frame, if_neg]
    · have := dualApp_smul (0 : Γ(X, U)) (0 : Γ(dual (fl.F l.rev), U)) le_rfl
      rw [zero_smul] at this
      rw [this]; simp
    · intro h
      have h₁ := congrArg Fin.val h
      have h₂ := a.isLt
      have h₃ := j.isLt
      have h₄ := l.is_le
      simp only [Fin.val_rev, Fin.val_castLE] at h₁ h₂
      omega
  choose s' hs' using fun j => (hex U _).1 (hz j)
  have inj (V : X.Opens) := QCoh.injective_app_of_mono (Limits.kernel.ι (dualMap (fl.ι l.rev))) V
  have hc (V : X.Opens) (h : V ≤ U) (a : Fin l → Γ(X, V)) :
      (Limits.kernel.ι (dualMap (fl.ι l.rev))).app V (Fintype.linearCombination Γ(X, V) (fun i => resM _ h (s' i)) a) =
        ∑ j, a j • resM _ h (hv.coord (Fin.castLE l.is_le j).rev) := by
    simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul, app_resM]
    exact Finset.sum_congr rfl fun j _ => congrArg (fun w => a j • resM _ h w) (hs' j)
  have hev (V : X.Opens) (h : V ≤ U) (a : Fin l → Γ(X, V)) (b : Fin N) :
      dualApp (∑ j, a j • resM _ h (hv.coord (Fin.castLE l.is_le j).rev)) le_rfl (resM F h (v b)) =
        if hb : (b.rev : ℕ) < l then a ⟨b.rev, hb⟩ else 0 := by
    simp only [dualApp_sum, LinearMap.sum_apply, dualApp_smul, dualApp_res, LinearMap.smul_apply,
      hv.dualApp_coord_frame, smul_eq_mul, mul_ite, mul_one, mul_zero, LB.resG_self]
    split_ifs with hb
    · rw [Finset.sum_eq_single ⟨b.rev, hb⟩ (fun j _ hj => if_neg fun e => hj (by subst e; simp [Fin.ext_iff]))
        (by simp), if_pos (by simp [Fin.ext_iff]; omega)]
    · exact Finset.sum_eq_zero fun j _ => if_neg fun e => hb (by subst e; simp)
  refine ⟨s', fun V h => ⟨(injective_iff_map_eq_zero _).2 fun a ha => funext fun j => ?_, fun w => ?_⟩, hs'⟩
  · have h₀ := hc V h a
    have h₁ := hev V h a (Fin.castLE l.is_le j).rev
    erw [ha, map_zero] at h₀
    have := dualApp_smul (0 : Γ(X, V)) (0 : Γ(dual F, V)) le_rfl
    rw [zero_smul] at this
    rw [← h₀, this] at h₁
    simpa using h₁.symm
  · refine ⟨fun j => dualApp ((Limits.kernel.ι (dualMap (fl.ι l.rev))).app V w) le_rfl
      (resM F h (v (Fin.castLE l.is_le j).rev)), inj V ((hc V h _).trans (hv.dual_ext h fun b => ?_))⟩
    rw [hev]
    split_ifs with hb
    · exact congrArg (fun c => dualApp _ le_rfl (resM F h (v c))) (Fin.rev_rev b)
    · have hb' : (b : ℕ) < l.rev := by
        have := b.isLt
        simp only [Fin.val_rev] at hb ⊢
        omega
      have h₀ : (dualMap (fl.ι l.rev)).app V ((Limits.kernel.ι (dualMap (fl.ι l.rev))).app V w) = 0 :=
        (hex V _).2 ⟨w, rfl⟩
      have h₁ := dualApp_dualMap (fl.ι l.rev) ((Limits.kernel.ι (dualMap (fl.ι l.rev))).app V w) le_rfl
        (resM _ h (s ⟨b, hb'⟩))
      have := dualApp_smul (0 : Γ(X, V)) (0 : Γ(dual (fl.F l.rev), V)) le_rfl
      rw [zero_smul] at this
      rw [h₀, this, app_resM, es] at h₁
      simpa using h₁

end Frames

section Measures

open GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem part_eq_restrict (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) :
    part ρ = (part ρ).restrict (⋃ c : AlgChart p σ 1, c.e.source) := by
  refine le_antisymm (iSup_le fun c => Measure.le_iff.2 fun A hA => ?_) Measure.restrict_le_self
  have hs := c.e.open_source.measurableSet
  rw [Measure.restrict_apply hA, ChartGlue.chartMeas_apply _ _ hA,
    ← ChartGlue.chartMeas_apply_of_subset _ (fun y => ENNReal.ofReal (ρ c y)) (hs.inter hA) inter_subset_left]
  refine (Measure.le_iff'.1 (le_iSup (fun c : AlgChart p σ 1 =>
    ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) c) _).trans (measure_mono fun y hy => ?_)
  exact ⟨hy.2, mem_iUnion.2 ⟨c, hy.1⟩⟩

theorem part_sum [SecondCountableTopology (CxPts p σ)] {J : Type} [Fintype J]
    {τ : J → AlgChart p σ 1 → CxPts p σ → ℝ} (h : ∀ j, IsDens (τ j))
    (h₀ : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source, 0 ≤ τ j c y) :
    ∑ j, part (τ j) = part fun c y => ∑ j, τ j c y := by
  have hs : IsDens fun c y => ∑ j, τ j c y := MixDens.IsDens.sum Finset.univ h
  obtain ⟨T, hT, hTS⟩ := TopologicalSpace.isOpen_iUnion_countable (fun c : AlgChart p σ 1 => c.e.source)
    fun c => c.e.open_source
  rw [part_eq_restrict fun c y => ∑ j, τ j c y, Finset.sum_congr rfl fun j _ => part_eq_restrict (τ j),
    show ∀ s : Set (CxPts p σ), ∑ j, (part (τ j)).restrict s = (∑ j, part (τ j)).restrict s from
      fun s => (map_sum (Measure.restrictₗ s) _ _).symm, ← hTS, Measure.restrict_biUnion_congr hT]
  intro c _
  ext A hA
  have hm := hA.inter c.e.open_source.measurableSet
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.finset_sum_apply,
    hs.part_apply c hm inter_subset_right, Finset.sum_congr rfl fun j _ => (h j).part_apply c hm inter_subset_right,
    ← lintegral_finset_sum']
  · refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hm inter_subset_right) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [c.e.left_inv hy.2]
    exact (ENNReal.ofReal_sum_of_nonneg fun j _ => h₀ j c y hy.2).symm
  · intro j _
    refine ENNReal.measurable_ofReal.comp_aemeasurable ((((h j).2 c).mono ?_).aemeasurable
      (ChartGlue.measurableSet_image _ hm inter_subset_right))
    rintro _ ⟨y, hy, rfl⟩
    exact c.e.map_source hy.2

end Measures

section Main

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ} {h : VMetric p E r}
  {σ : k →+* ℂ}

theorem bcDens_step (H : h.IsCInf) {fl : Vert.Flag E r} {U : X.Opens} {v : Fin r → Γ(E, U)} (hv : Spans fl U v)
    (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) (hU : y ∈ ptsIn p σ U)
    {K : CxPts p σ → Matrix (Fin r) (Fin r) ℂ} (hK : ∀ z ∈ ptsIn p σ U, (h.met σ).gram v z = K z) (i : Fin r) :
    ((h.stepMet fl i).met σ).bcDens (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) c y =
      2 * diagVal (extTrace (fun w => (K (c.e.symm w)).submatrix (emb i) (emb i)) (c.e y))
        (EuclideanSpace.single 0 1) := by
  obtain ⟨s, t, h₁, h₂, h₃⟩ := hv.exists_adaptedChart i
  let a : VBExt.AdaptedChart (VMetric.stepSeq fl i) i 1 := ⟨U, s, t, h₁, h₂⟩
  rw [Met.bcDens_eq (h := (h.stepMet fl i).met σ) _ _ _ a c
    ((H σ).restrict (fl.isSubbundle i.succ) (fl.isVB i.succ)) hy hU, Met.bcForm, extTrace_congr]
  refine eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds
    (ChartGlue.mem_over c.e hy hU)) fun w hw => ?_
  ext j l
  beta_reduce
  rw [submatrix_apply, ← hK _ hw.2, Met.gram, Met.gram, of_apply, of_apply, ← h₃, ← h₃]
  exact Met.form_restrict _ (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hw.2

theorem sum_bcDens_dualFlag (H : h.IsCInf) (fl : Vert.Flag E r) (c : AlgChart p σ 1) {y : CxPts p σ}
    (hy : y ∈ c.e.source) :
    ∑ i, ((h.dual.stepMet (DualFlag.dualFlag fl) i).met σ).bcDens (VMetric.stepSeq_shortExact _ i)
        ((DualFlag.dualFlag fl).isVB i.castSucc) ((DualFlag.dualFlag fl).isVB_gr i) c y =
      ∑ i, ((h.stepMet fl i).met σ).bcDens (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc)
        (fl.isVB_gr i) c y := by
  obtain ⟨U, v, hU, hs⟩ := exists_spans fl (y.1 (IsLocalRing.closedPoint ℂ))
  have hU' : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  have hv := isFrame_of_spans hs
  let cE : Chart E r := ⟨U, v, hv⟩
  have e₁ (z) (hz : z ∈ ptsIn p σ U) : (h.met σ).gram v z = (h.met σ).G cE z :=
    Matrix.ext fun a b => (h.met σ).form_frame cE hz a b
  have e₂ (z) (hz : z ∈ ptsIn p σ U) :
      (h.dual.met σ).gram (fun j => hv.coord j.rev) z = revDual ((h.met σ).G cE z) := by
    rw [revDual, ← (h.met σ).dual_G cE hz]
    exact Matrix.ext fun a b => (h.met σ).dual.form_frame cE.dual hz a.rev b.rev
  simp only [bcDens_step H hs c hy hU' e₁, bcDens_step H.dual (spans_dualFlag hs hv) c hy hU' e₂,
    ← Finset.mul_sum, diagVal, ← Complex.re_sum]
  rw [sum_extTrace_revDual (K := fun w => (h.met σ).G cE (c.e.symm w))
    (((H σ cE y hU').mContDiffAt c hy).of_le (by norm_cast))
    (eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds
      (ChartGlue.mem_over c.e hy hU')) fun w hw => (h.met σ).posDef cE _ hw.2)]

end Main

theorem sum_bcMeas_dualFlag : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X]
    (E : X.Modules) (r : ℕ) (h : VMetric p E r) (_ : h.IsCInf) (fl : Vert.Flag E r) (σ : k →+* ℂ), IsRegSurf p →
    ∑ i, ((h.dual.stepMet (GlobalTheory.DualFlag.dualFlag fl) i).met σ).bcMeas
        (VMetric.stepSeq_shortExact (GlobalTheory.DualFlag.dualFlag fl) i) ((GlobalTheory.DualFlag.dualFlag fl).isVB i.castSucc)
        ((GlobalTheory.DualFlag.dualFlag fl).isVB_gr i) univ =
      ∑ i, ((h.stepMet fl i).met σ).bcMeas (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc)
        (fl.isVB_gr i) univ := by
  intro k _ X p _ E r h H fl σ hX
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have key {E : X.Modules} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) :=
    part_sum (τ := fun i c y => ((h.stepMet fl i).met σ).bcDens (VMetric.stepSeq_shortExact fl i)
      (fl.isVB i.castSucc) (fl.isVB_gr i) c y)
      (fun i => CurveDens.isDens_bcDens _ _ _ ((H σ).restrict (fl.isSubbundle i.succ) (fl.isVB i.succ)))
      fun i c y hy => Met.bcDens_nonneg _ _ _ c ((H σ).restrict (fl.isSubbundle i.succ) (fl.isVB i.succ)) hy
  simp only [CurveDens.bcMeas_eq_part, ← Measure.finset_sum_apply]
  rw [key H fl, key H.dual, CurveDens.part_congr fun c y hy => sum_bcDens_dualFlag H fl c hy]

end GlobalTheory.DualFlagBc
