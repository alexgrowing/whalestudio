import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFrameFormNormSqEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralRankTwoStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineMeet

open Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.Points
open scoped ContDiff ComplexOrder

theorem pull_ofValues {n m : ℕ} (L : V n →L[ℂ] V m) {α : V m → V m → ℂ} (hα : IsSesq α) :
    pull L (ofValues α : Alt m) = ofValues (fun ξ η => α (L ξ) (L η)) := by
  simp only [ofValues, GlobalTheory.LineForm.OmReal.sesq_expand hα (L _), AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul,
    sym, map_sum, map_smul, map_mul, (pull_dz L _).1, (pull_dz L _).2, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]

theorem form_submatrix {r r' : Type} [Fintype r] [Fintype r'] (e : r' ≃ r) (M : Matrix r r ℂ) (u u' : r → ℂ) :
    form (M.submatrix e e) (u ∘ e) (u' ∘ e) = form M u u' := by
  simp only [form_eq_sum, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun a _ => by rw [← e.sum_comp]

theorem ddc_fn_apply {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {f : M → ℝ}
    (hf : A.SmoothOn Set.univ fun y => (f y : ℂ)) (x : A.Pt) :
    A.ddc (A.fn f) x = ofValues (ddc (fun v => f (x.ch.symm v)) x.crd) := by
  have hn : x.ch.target ∈ 𝓝 x.crd := x.ch.open_target.mem_nhds (x.ch.map_source x.2)
  have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf x.1.1)
  have h2 : ContDiffOn ℝ ∞ (fun v => f (x.ch.symm v)) x.ch.target :=
    (h1.mono fun v hv => ⟨hv, trivial⟩).congr fun v _ => by simp
  rw [← delAt_dbarAt_fun ((h2.contDiffAt hn).of_le (by norm_cast))]
  refine GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq A _ x _ ?_
  filter_upwards [hn] with v hv
  rw [HolAtlas.loc, dif_pos hv]
  rfl

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {D D' : ℕ}

theorem gram_and_cos {π : Y ⟶ B} {w : π ≫ q = p} {E : B.Modules} (h : VMetric q E 2) {flB : Vert.Flag E 2}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {σ : k →+* ℂ} {v : CxPts p σ → ℝ}
    (hv : GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v)
    (a : VBExt.AdaptedChart (lineSC fl) 1 1) (b : VBExt.AdaptedChart (lineSC flB) 1 1) {y : CxPts p σ}
    (ha : y ∈ ptsIn p σ a.U) (hb : PtsOver.map π w _ y ∈ ptsIn q σ b.U)
    {A K : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ}
    (hA : A = ((((b.mid (lineSC_shortExact flB)).pull (h.met σ).isVB π).tr p σ (a.mid (lineSC_shortExact fl)) y).submatrix
      finSumFinEquiv finSumFinEquiv))
    (hK : K = (h.met σ).gram b.frame (PtsOver.map π w _ y)) :
    ((h.pull π w).met σ).gram a.frame y = chg A K ∧
      ‖form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0))‖ ^ 2 =
        v y * (chg A K (Sum.inl 0) (Sum.inl 0)).re * (K (Sum.inl 0) (Sum.inl 0)).re := by
  have hS := lineSC_shortExact flB
  have hS' := lineSC_shortExact fl
  set m := (h.pull π w).met σ with hm
  let c : Chart E 2 := b.mid hS
  let c' : Chart ((Scheme.Modules.pullback π).obj E) 2 := c.pull (h.met σ).isVB π
  have hc' : y ∈ ptsIn p σ c'.U := hb
  have hG : m.G c' y = (h.met σ).G c (PtsOver.map π w _ y) := (h.met σ).pull_G π w c hb
  have hK' : K = (m.G c' y).submatrix (finSumFinEquiv (m := 1) (n := 1)) (finSumFinEquiv (m := 1) (n := 1)) := by
    rw [hG, hK]
    exact Met.gram_frame (S := lineSC flB) (r := 1) (s := 1) (h.met σ) hS b hb
  have e₁ : m.gram a.frame y = chg A K := by
    rw [hK', hA, chg_submatrix]
    refine (Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) m hS' a ha).trans ?_
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.submatrix (finSumFinEquiv (m := 1) (n := 1))
      (finSumFinEquiv (m := 1) (n := 1))) (m.trans c' (a.mid hS') y hc')
  refine ⟨e₁, ?_⟩
  have hy : y ∈ ptsIn p σ (a.U ⊓ π ⁻¹ᵁ b.U) := mem_ptsIn_inf.2 ⟨ha, hb⟩
  have key := hv (a.U ⊓ π ⁻¹ᵁ b.U) (Twist.resM _ inf_le_left (a.e 0))
    (QCoh.pullbackSections π _ inf_le_right (b.e 0)) y hy
  rw [QCoh.pullback_map_app_pullbackSections, Twist.app_resM, m.form_resM _ _ _ hy] at key
  have e₂ : m.form (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0)))
      (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0))) y =
      K (Sum.inl 0) (Sum.inl 0) := by
    rw [hK]
    exact (h.met σ).form_pull π w _ _ _ hy
  have e₃ : m.form ((fl.ι 1).app a.U (a.e 0)) ((fl.ι 1).app a.U (a.e 0)) y = chg A K (Sum.inl 0) (Sum.inl 0) := by
    rw [← e₁]; rfl
  have e₄ : m.form (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0)))
      (Twist.resM _ (inf_le_left : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((fl.ι 1).app a.U (a.e 0))) y =
      form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0)) := by
    rw [m.form_eq c' hc' _ _ hy, Chart.crd_pull c _ π w _ _ hy hb, Chart.crd_resM _ _ _ hy, hK',
      ← form_submatrix (finSumFinEquiv (m := 1) (n := 1))]
    congr 1
    · funext i
      refine (b.crd_frame hS hb i (.inl 0)).trans ?_
      simp [Pi.single_apply, one_apply]
    · funext i
      rw [hA]
      simp [Chart.tr, VBExt.AdaptedChart.mid, VBExt.AdaptedChart.frame, c', c, -finSumFinEquiv_apply_left]
  rw [e₂, e₃, e₄] at key
  exact key

theorem ddc_mul_omF_sub (hB : IsRegVar q D) (hY : IsRegVar p D') {π : Y ⟶ B} {w : π ≫ q = p} {E : B.Modules}
    {h : VMetric q E 2} (H : h.IsCInf) {flB : Vert.Flag E 2}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {σ : k →+* ℂ} {v : CxPts p σ → ℝ}
    (hv : GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v)
    (hs : (hY.atlas σ).SmoothOn Set.univ fun y => ((1 - v y : ℝ) : ℂ)) (x : (hY.atlas σ).Pt) (hx1 : v x.pt = 1) :
    (hY.atlas σ).ddc ((hY.atlas σ).fn fun y => 1 - v y) x *
      ((omF hY σ (h.pull π w) fl x : Alt D') - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) x) = 0 := by
  have hS := lineSC_shortExact flB
  have hS' := lineSC_shortExact fl
  set f : CxPts p σ → CxPts q σ := PtsOver.map π w _ with hf
  have hm : ∀ z, (f z).1 = z.1 ≫ π := fun _ => rfl
  let x' : (hB.atlas σ).Pt := ⟨(_, f x.pt), ((hB.atlas σ).cover (f x.pt)).choose_spec⟩
  let a := frameAt fl x.pt
  let b := frameAt flB (f x.pt)
  have ha : x.pt ∈ ptsIn p σ a.U := mem_frameAt fl x.pt
  have hb : f x.pt ∈ ptsIn q σ b.U := mem_frameAt flB (f x.pt)
  let c' : Chart ((Scheme.Modules.pullback π).obj E) 2 := (b.mid hS).pull (h.met σ).isVB π
  have hc' : x.pt ∈ ptsIn p σ c'.U := hb
  let φ := x'.ch ∘ f ∘ x.ch.symm
  let G : V D → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun u => (h.met σ).gram b.frame (x'.ch.symm u)
  let A : V D' → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun u =>
    (c'.tr p σ (a.mid hS') (x.ch.symm u)).submatrix (finSumFinEquiv (m := 1) (n := 1)) (finSumFinEquiv (m := 1) (n := 1))
  have e : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have ho := ChartGlue.isOpen_over x.ch (x'.ch.open_source.preimage (continuous_of_comp hm))
  have hx := ho.mem_nhds (ChartGlue.mem_over x.ch x.2 (show x.pt ∈ f ⁻¹' x'.ch.source from x'.2))
  have hφ : AnalyticAt ℂ φ x.crd :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo_map hm x.1.1 x'.1.1) hx
  have hφx : φ x.crd = x'.crd := congrArg (fun z => x'.ch (f z)) e
  have hG : MContDiffAt ∞ G (φ x.crd) := by
    rw [hφx]; exact ((H σ).gram b.frame hb).mContDiffAt x'.1.1 x'.2
  have hGp : ∀ᶠ u in 𝓝 (φ x.crd), (G u).PosDef := by
    rw [hφx]; exact Met.eventually_posDef (S := lineSC flB) (r := 1) (s := 1) (h.met σ) hS b x'.1.1 x'.2 hb
  have hG1 : MContDiffAt 1 G (φ x.crd) := hG.of_le (by norm_cast)
  have e₁ : pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) x = ofValues (extTrace (fun u => G (φ u)) x.crd) := by
    change pull (fderiv ℂ φ x.crd) (ofValues (extTrace G x'.crd) : Alt D) = _
    rw [← hφx, pull_ofValues _ (OmReal.isSesq_extTrace hG1 hGp)]
    refine congrArg (fun α : V D' → V D' → ℂ => (ofValues α : Alt D')) (funext fun ξ => funext fun η => ?_)
    rw [extTrace_comp_holo hG1 hGp hφ.contDiffAt]
  have hloc : ∀ᶠ u in 𝓝 x.crd, ((h.pull π w).met σ).gram a.frame (x.ch.symm u) = chg (A u) (G (φ u)) ∧
      ‖form (G (φ u)) (Pi.single (Sum.inl 0) 1) (fun i => A u i (Sum.inl 0))‖ ^ 2 =
        v (x.ch.symm u) * (chg (A u) (G (φ u)) (Sum.inl 0) (Sum.inl 0)).re * (G (φ u) (Sum.inl 0) (Sum.inl 0)).re := by
    filter_upwards [hx, (ChartGlue.isOpen_over x.ch (isOpen_ptsIn a.U)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha),
      (ChartGlue.isOpen_over x.ch (isOpen_ptsIn c'.U)).mem_nhds (ChartGlue.mem_over x.ch x.2 hc')] with u h₁ h₂ h₃
    exact gram_and_cos h hv a b h₂.2 h₃.2 rfl (congrArg ((h.met σ).gram b.frame) (x'.ch.left_inv h₁.2))
  have e₂ : (omF hY σ (h.pull π w) fl x : Alt D') = ofValues (extTrace (fun u => chg (A u) (G (φ u))) x.crd) := by
    rw [← extTrace_congr (hloc.mono fun u hu => hu.1)]
    rfl
  rw [e₁, e₂, ddc_fn_apply _ hs]
  refine GlobalTheory.T.hermitian_frame_form_norm_sq_eq D' (fun u => G (φ u)) A (fun u => v (x.ch.symm u)) x.crd
    (fun i j => ((hG i j).of_le (by norm_cast)).comp x.crd (hφ.contDiffAt.restrict_scalars ℝ))
    (hφ.continuousAt.eventually hGp) (fun i j => ?_) ?_ (by rw [e, hx1]) (hloc.mono fun u hu => hu.2)
  · exact GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo x.1.1 _ _)
      ((ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds
        (ChartGlue.mem_over x.ch x.2 (mem_ptsIn_inf.2 ⟨ha, hc'⟩)))
  · simp only [A, det_submatrix_equiv_self, e]
    exact (isUnit_iff_isUnit_det _).1 (c'.isUnit_tr (a.mid hS') hc' ha)

theorem tendsto_integral_conc : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) *
      ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) * (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (K) * (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)))))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K
  obtain ⟨-, -, hsm⟩ := GlobalTheory.CosSqSmooth.cosSq_smooth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hs : (hY.atlas σ).SmoothOn Set.univ fun y => ((1 - v y : ℝ) : ℂ) := fun i =>
    ((contDiffOn_const (c := (1 : ℂ))).sub (hsm i)).congr fun u _ => by simp
  obtain ⟨-, halg, -, hev, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hY.atlas σ)
  obtain ⟨hc1, hom, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨-, homB, hpl⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  have hf := (hY.atlas σ).isForm_fn hs
  have hP (P : MvPolynomial (Fin 5) ℝ) := (hev _ (fun i => c1F hY σ (fam5 π w H flB fl A i)) P
    fun i => (hc1 _ (fam5 π w H flB fl A i)).1.1).1
  have hdb := (halg 0 _ _ hf hf).2.2.2.2.1
  have hdd := (halg 0 _ _ hdb hdb).2.2.2.1
  have hddc : (hY.atlas σ).IsForm ((hY.atlas σ).ddc ((hY.atlas σ).fn fun y => 1 - v y)) :=
    (halg kappa _ _ hdd hdd).2.2.1
  have h₁ := (hom _ (h.pull π w) (H.pull π w) fl fl).1.1
  have h₂ : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) :=
    ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _ (hpl Y p _ hY π w).1).2 0 _ 0).2.2.2
      (homB E h H flB flB).1.1).1
  have h₃ : (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) -
      pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (pullF hB hY σ π w _)]
    exact (halg 0 _ _ h₁ (halg (-1) _ _ h₂ h₂).2.2.1).1
  simp only [mul_assoc ((hY.atlas σ).fn fun y => _ / (1 - v y + _) ^ 2)]
  refine GlobalTheory.T.flag_bundle_chern_integral_rank_two k B Y q p d hB hY π w E h H flB fl hfl A σ v hv _
    (halg 0 _ _ (halg 0 _ _ hddc (halg 0 _ _ hf (hP _)).2.1).1 (halg 0 _ _ (hP K) h₃).2.1).2.1 fun x hx => ?_
  have key := ddc_mul_omF_sub hB hY H hv hs x hx
  have hz : (hY.atlas σ).fn (fun y => 1 - v y) x = 0 := by simp [HolAtlas.fn, hx]
  have hc : ∀ β : Alt (d + 1), β * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K x =
      evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K x * β := fun β =>
    Subalgebra.mem_center_iff.1 (Subtype.property _) β
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, hz, zero_mul, add_zero]
  rw [← mul_assoc, hc, mul_assoc]
  erw [key]
  simp [dens]

end GlobalTheory.LineMeet
