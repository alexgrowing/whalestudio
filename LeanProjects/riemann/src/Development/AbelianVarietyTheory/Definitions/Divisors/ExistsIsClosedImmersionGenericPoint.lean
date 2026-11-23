import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxA

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V cHess leviV)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open scoped ContDiff ENNReal

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

namespace CxPts

variable {y : CxPts p σ} {f f' : CxPts p σ → ℝ}

def CInfAt (f : CxPts p σ → ℝ) (y : CxPts p σ) : Prop :=
  ∃ (W : X.Opens) (ι : Type) (_ : Fintype ι) (g : ι → Γ(X, W)) (F : (ι → ℂ) → ℝ) (O : Set (ι → ℂ)),
    y ∈ ptsIn p σ W ∧ IsOpen O ∧ (fun a => ev p σ W (g a) y) ∈ O ∧ ContDiffOn ℝ ∞ F O ∧
      f =ᶠ[𝓝 y] fun z => F fun a => ev p σ W (g a) z

theorem CInfAt.congr (h : CInfAt f y) (e : f' =ᶠ[𝓝 y] f) : CInfAt f' y :=
  have ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, e.trans h₅⟩

theorem cInfAt_const (c : ℝ) (y : CxPts p σ) : CInfAt (fun _ => c) y :=
  ⟨⊤, Empty, inferInstance, Empty.elim, fun _ => c, univ, mem_ptsIn_top, isOpen_univ, trivial,
    contDiffOn_const, EventuallyEq.rfl⟩

theorem CInfAt.comp₂ (h : CInfAt f y) (h' : CInfAt f' y) {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    CInfAt (fun z => G (f z, f' z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  obtain ⟨W', ι', _, g', F', O', h₁', h₂', h₃', h₄', h₅'⟩ := h'
  have hW := mem_ptsIn_inf.2 ⟨h₁, h₁'⟩
  have cl : ContDiff ℝ ∞ fun (v : ι ⊕ ι' → ℂ) a => v (.inl a) :=
    contDiff_pi.2 fun a => contDiff_apply _ _ _
  have cr : ContDiff ℝ ∞ fun (v : ι ⊕ ι' → ℂ) a => v (.inr a) :=
    contDiff_pi.2 fun a => contDiff_apply _ _ _
  refine ⟨W ⊓ W', ι ⊕ ι', inferInstance,
    Sum.elim (fun a => resG X inf_le_left (g a)) fun a => resG X inf_le_right (g' a),
    fun v => G (F fun a => v (.inl a), F' fun a => v (.inr a)),
    (fun v a => v (.inl a)) ⁻¹' O ∩ (fun v a => v (.inr a)) ⁻¹' O', hW,
    (h₂.preimage cl.continuous).inter (h₂'.preimage cr.continuous), ⟨?_, ?_⟩,
    hG.comp_contDiffOn ((h₄.comp cl.contDiffOn fun _ hv => hv.1).prodMk
      (h₄'.comp cr.contDiffOn fun _ hv => hv.2)), ?_⟩
  · simpa only [mem_preimage, Sum.elim_inl, ev_res _ hW] using h₃
  · simpa only [mem_preimage, Sum.elim_inr, ev_res _ hW] using h₃'
  · filter_upwards [h₅, h₅', (isOpen_ptsIn _).mem_nhds hW] with z e e' hz
    simp only [Sum.elim_inl, Sum.elim_inr, ev_res _ hz, e, e']

theorem CInfAt.add (h : CInfAt f y) (h' : CInfAt f' y) : CInfAt (fun z => f z + f' z) y :=
  h.comp₂ h' (G := fun x => x.1 + x.2) (contDiff_fst.add contDiff_snd)

theorem CInfAt.const_mul (h : CInfAt f y) (c : ℝ) : CInfAt (fun z => c * f z) y :=
  h.comp₂ h (G := fun x => c * x.1) (contDiff_const.mul contDiff_fst)

theorem CInfAt.neg (h : CInfAt f y) : CInfAt (fun z => -f z) y :=
  h.comp₂ h (G := fun x => -x.1) contDiff_fst.neg

theorem CInfAt.continuousAt (h : CInfAt f y) : ContinuousAt f y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ContinuousAt.congr ?_ h₅.symm
  exact ContinuousAt.comp (f := fun z a => ev p σ W (g a) z)
    (h₄.continuousOn.continuousAt (h₂.mem_nhds h₃)) (continuousAt_pi.2 fun a =>
      (continuousOn_ev (g a)).continuousAt ((isOpen_ptsIn W).mem_nhds h₁))

theorem ev_app {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (W : X.Opens) (g : Γ(X, W))
    (z : CxPts q σ) : ev q σ (π ⁻¹ᵁ W) (π.app W g) z = ev p σ W g (PtsOver.map π hπ _ z) :=
  (valR_comp z.1 π W g).symm

theorem CInfAt.pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) {z : CxPts q σ}
    (h : CInfAt f (PtsOver.map π hπ _ z)) : CInfAt (fun w => f (PtsOver.map π hπ _ w)) z := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨π ⁻¹ᵁ W, ι, inferInstance, fun a => π.app W (g a), F, O, h₁, h₂, ?_, h₄, ?_⟩
  · simpa only [ev_app π hπ] using h₃
  · simp only [ev_app π hπ]
    exact (PtsOver.continuous_map π hπ _).continuousAt.eventually h₅

variable {D : ℕ}

theorem contDiffOn_chart {S : Set (CxPts p σ)} (h : ∀ y ∈ S, CInfAt f y) (c : AlgChart p σ D) :
    ContDiffOn ℝ ∞ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) := fun v hv => by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h _ hv.2
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) W)
  have hg : ContDiffAt ℝ ∞ (fun w a => ev p σ W (g a) (c.e.symm w)) v := contDiffAt_pi.2 fun a =>
    (contDiffOn_real ho (c.holo W (g a))).contDiffAt (ho.mem_nhds ⟨hv.1, h₁⟩)
  exact (((h₄.contDiffAt (h₂.mem_nhds h₃)).comp v hg).congr_of_eventuallyEq
    ((c.e.continuousAt_symm hv.1).eventually h₅)).contDiffWithinAt

theorem cInfAt_of_chart {S : Set (CxPts p σ)} (hS : IsOpen S) (c : AlgChart p σ D)
    (h : ContDiffOn ℝ ∞ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S)) (hy : y ∈ c.e.source)
    (hyS : y ∈ S) : CInfAt f y := by
  have hc (z) (hz : z ∈ c.e.source) : WithLp.toLp 2 (fun a => ev p σ c.U (c.x a) z) = c.e z := by
    ext a; exact (c.apply_eq z hz a).symm
  have ht : ContDiff ℝ ∞ (WithLp.toLp 2 : (Fin D → ℂ) → V D) := PiLp.contDiff_toLp
  refine ⟨c.U, Fin D, inferInstance, c.x, (f ∘ c.e.symm) ∘ WithLp.toLp 2,
    WithLp.toLp 2 ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' S), c.source_subset hy,
    (isOpen_over c.e hS).preimage ht.continuous, ?_, h.comp ht.contDiffOn fun _ hv => hv, ?_⟩
  · rw [mem_preimage, hc y hy]
    exact mem_over c.e hy hyS
  · filter_upwards [c.e.open_source.mem_nhds hy] with z hz
    simp only [Function.comp_apply, hc z hz, c.e.left_inv hz]

theorem cInfAt_iff_smoothOn (R : AnRead p σ D) {S : Set (CxPts p σ)} (hS : IsOpen S) :
    (∀ y ∈ S, CInfAt f y) ↔ R.SmoothOn S f :=
  ⟨fun h _ => contDiffOn_chart h _, fun h y hy =>
    have ⟨i, hi⟩ := R.cover y
    cInfAt_of_chart hS _ (h i) hi hy⟩

end CxPts

namespace Weight

variable {A B : LB X} {φ : Weight p σ B} {D : ℕ}

def IsCInf (φ : Weight p σ B) : Prop := ∀ i, ∀ y ∈ ptsIn p σ (B.U i), CInfAt (φ.φ i) y

theorem isCInf_iff_isSmooth (R : AnRead p σ D) : φ.IsCInf ↔ φ.IsSmooth R :=
  forall_congr' fun _ => cInfAt_iff_smoothOn R (isOpen_ptsIn _)

theorem IsCInf.addFn (h : φ.IsCInf) {u : CxPts p σ → ℝ} (hu : ∀ y, CInfAt u y) :
    (φ.addFn u).IsCInf := fun i y hy => (h i y hy).add (hu y)

theorem IsCInf.tens {ψ : Weight p σ A} (h' : ψ.IsCInf) (h : φ.IsCInf) : (ψ.tens φ).IsCInf :=
  fun i y hy => (h' i.1 y (mem_ptsIn_inf.1 hy).1).add (h i.2 y (mem_ptsIn_inf.1 hy).2)

theorem IsCInf.dual (h : φ.IsCInf) : φ.dual.IsCInf := fun i y hy => (h i y hy).neg

theorem IsCInf.zpow (h : φ.IsCInf) (n : ℤ) : (φ.zpow n).IsCInf := fun j y hy =>
  ((h _ y (mem_pow_iff.1 hy)).const_mul n).congr (.of_forall fun z => φ.zpow_φ n j z)

theorem IsCInf.pull (h : φ.IsCInf) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (φ.pull π hπ).IsCInf := fun j z hz =>
  (CInfAt.pull π hπ (h _ _ (mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z)
    (fun _ => rfl) hz PUnit.unit))).congr (.of_forall fun w => φ.pull_φ π hπ j w)

theorem isCInf_ofFun {u : CxPts p σ → ℝ} (hu : ∀ y, CInfAt u y) : (ofFun u).IsCInf :=
  fun _ y _ => hu y

theorem isCInf_fsBasis {α : Type} [Fintype α] [DecidableEq α] (hB : B.IsLB) (b : α → B.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (M : Matrix α α ℂ) (hM : M.det ≠ 0) :
    (fsBasis p σ hB b hb M hM).IsCInf := fun i y hy => by
  have hs : ContDiff ℝ ∞ fun v : α → ℂ => ∑ a, ‖∑ j, M j a * v j‖ ^ 2 :=
    ContDiff.sum fun a _ => (ContDiff.sum fun j _ =>
      contDiff_const.mul (contDiff_apply ℝ ℂ j)).norm_sq ℂ
  refine ⟨B.U i, α, inferInstance, fun j => (b j).f i,
    fun v => Real.log (∑ a, ‖∑ j, M j a * v j‖ ^ 2), {v | ∑ a, ‖∑ j, M j a * v j‖ ^ 2 ≠ 0}, hy,
    isOpen_ne_fun hs.continuous continuous_const, ?_, hs.contDiffOn.log fun _ h => h,
    .of_forall fun z => fsBasis_φ hB b hb M hM i z⟩
  have := ((noCommonZero_combVal (p := p) (σ := σ) hb hM).sum_pos hy).ne'
  simp only [combVal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this

theorem IsCInf.continuous_nsq (h : φ.IsCInf) (s : B.Sec) : Continuous (φ.nsq (secVal p σ s)) :=
  continuous_iff_continuousAt.2 fun y => by
  have hi := mem_pick φ.isLB y
  have ho := (isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi
  refine ((((continuousOn_ev (s.f _)).continuousAt ho).norm.pow 2).mul
    (h _ y hi).continuousAt.neg.rexp).congr ?_
  exact eventually_of_mem ho fun z hz => (φ.nsq_eq (secVal_mem s) hz).symm

def SemiPosReg (φ : Weight p σ B) (D : ℕ) : Prop :=
  ∀ (i : B.ι) (c : AlgChart p σ D), ∀ y ∈ c.e.source ∩ ptsIn p σ (B.U i), ∀ ξ : Fin D → ℂ,
    0 ≤ (leviV D (fun v => (φ.φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re

theorem IsCInf.contDiffAt (h : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) {i : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) :
    ContDiffAt ℝ 2 (fun v => φ.φ i (c.e.symm v)) (c.e y) :=
  ((contDiffOn_chart (h i) c).contDiffAt
    ((isOpen_over c.e (isOpen_ptsIn _)).mem_nhds (mem_over c.e hy hi))).of_le (by norm_cast)

theorem semiPosReg_iff (h : φ.IsCInf) (R : AnRead p σ D) : φ.SemiPosReg D ↔ φ.SemiPos R := by
  refine ⟨fun H i c => H i _, fun H i c y hy ξ => ?_⟩
  obtain ⟨a, ha⟩ := R.cover y
  set c' := R.chart a
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy.1 ha
  have e : (fun v => (φ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
      (fun v => (φ.φ i (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
    eventually_of_mem (ho.mem_nhds hm) fun v hv => by
      simp only [Function.comp_apply, c'.e.left_inv hv.2]
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy.1)
  have hd : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) := contDiffAt_euclidean.2 fun b =>
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho
      (differentiableOn_euclidean.1 (c.holo_trans c') b)).contDiffAt (ho.mem_nhds hm)).of_le
      (by norm_cast)
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e, ReciprocityTheory.L2DbarEstimates.Y.leviV_comp (e₂ ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h.contDiffAt c' ha hy.2)) hd, e₂]
  exact H i a y ⟨ha, hy.2⟩ _

end Weight

namespace AlgChart

variable {B : LB X} {D : ℕ} (c c' : AlgChart p σ D) (φ : Weight p σ B) {y : CxPts p σ}

def hess (i : B.ι) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  cHess D (fun v => (φ.φ i (c.e.symm v) : ℂ)) (c.e y)

def chernDens (y : CxPts p σ) : ℝ :=
  D.factorial / Real.pi ^ D * (c.hess φ (pick φ.isLB y) y).det.re

variable {φ}

theorem hess_eq (h : φ.IsCInf) (hy : y ∈ c.e.source) {i j : B.ι} (hi : y ∈ ptsIn p σ (B.U i))
    (hj : y ∈ ptsIn p σ (B.U j)) : c.hess φ j y = c.hess φ i y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B.U j))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, hj⟩)
  have hg := c.holo _ (B.g i j).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ B.U j),
      (ev p σ _ (B.g i j).val ∘ c.e.symm) v ≠ 0 := fun v hv => ev_ne_zero hv.2 (B.g i j).isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h i) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    (contDiffOn_log_normSq ho hg h0) (-1) hm
  have e₀ : cHess D (fun w => ((Real.log (‖(ev p σ _ (B.g i j).val ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [φ.trans i j _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, neg_one_mul, sub_eq_add_neg]
  rfl

theorem chernDens_eq (h : φ.IsCInf) (hy : y ∈ c.e.source) {i : B.ι}
    (hi : y ∈ ptsIn p σ (B.U i)) :
    c.chernDens φ y = D.factorial / Real.pi ^ D * (c.hess φ i y).det.re := by
  rw [chernDens, c.hess_eq h hy hi (mem_pick _ y)]

theorem chernDens_trans (h : φ.IsCInf) (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    c.chernDens φ y = ‖transDet c.e c'.e y‖ ^ 2 * c'.chernDens φ y := by
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have e : (fun v => (φ.φ (pick φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
      (fun v => (φ.φ (pick φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
    eventually_of_mem (ho.mem_nhds hm) fun v hv => by
      simp only [Function.comp_apply, c'.e.left_inv hv.2]
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  rw [chernDens, chernDens, hess, hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
    ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (c.holo_trans c') (e₂ ▸
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h.contDiffAt c' hy' (mem_pick _ y))), e₂,
    Complex.re_ofReal_mul, transDet]
  ring

theorem chernDens_nonneg (h : φ.IsCInf) (h' : φ.SemiPosReg D) (hy : y ∈ c.e.source) :
    0 ≤ c.chernDens φ y :=
  mul_nonneg (by positivity) (ReciprocityTheory.L2DbarEstimates.Y.cmpb_det_nonneg
    (h.contDiffAt c hy (mem_pick _ y)) (h' _ c y ⟨hy, mem_pick _ y⟩))

theorem chernDens_zero (c : AlgChart p σ 0) (y : CxPts p σ) : c.chernDens φ y = 1 := by
  simp [chernDens]

theorem chernDens_addFn_const (t : ℝ) (y : CxPts p σ) :
    c.chernDens (φ.addFn fun _ => t) y = c.chernDens φ y := by
  have := ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_add_const
    (fun v => (φ.φ (pick φ.isLB y) (c.e.symm v) : ℂ)) t (c.e y)
  simp only [chernDens, hess, Weight.addFn, Complex.ofReal_add, this]

end AlgChart

namespace Weight

variable {B : LB X} (φ : Weight p σ B) (D : ℕ)

def chernPart (ε : ℤˣ) : Measure (CxPts p σ) :=
  glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)

def ChernIntegrableOn (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) : Prop :=
  IntegrableOn f S (φ.chernPart D 1) ∧ IntegrableOn f S (φ.chernPart D (-1))

def chernInt (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) : ℝ :=
  ∫ y in S, f y ∂φ.chernPart D 1 - ∫ y in S, f y ∂φ.chernPart D (-1)

variable {φ D} {S : Set (CxPts p σ)} {f g : CxPts p σ → ℝ}

theorem ChernIntegrableOn.congr (h : φ.ChernIntegrableOn D S f) (hS : MeasurableSet S)
    (e : EqOn f g S) : φ.ChernIntegrableOn D S g := ⟨h.1.congr_fun e hS, h.2.congr_fun e hS⟩

theorem chernInt_congr (hS : MeasurableSet S) (e : EqOn f g S) :
    φ.chernInt D S f = φ.chernInt D S g := by
  rw [chernInt, chernInt, setIntegral_congr_fun hS e, setIntegral_congr_fun hS e]

theorem chernInt_add (hf : φ.ChernIntegrableOn D S f) (hg : φ.ChernIntegrableOn D S g) :
    φ.chernInt D S (fun y => f y + g y) = φ.chernInt D S f + φ.chernInt D S g := by
  rw [chernInt, chernInt, chernInt, integral_add hf.1 hg.1, integral_add hf.2 hg.2]
  ring

theorem chernInt_const_mul (a : ℝ) : φ.chernInt D S (fun y => a * f y) = a * φ.chernInt D S f := by
  rw [chernInt, chernInt, integral_const_mul, integral_const_mul, mul_sub]

theorem chernPart_addFn_const (t : ℝ) (ε : ℤˣ) :
    (φ.addFn fun _ => t).chernPart D ε = φ.chernPart D ε := by
  simp only [chernPart, AlgChart.chernDens_addFn_const]

theorem chernPart_eq_zero (ε : ℤˣ) (hS : MeasurableSet S)
    (h : ∀ c : AlgChart p σ D, Disjoint c.e.source S) : φ.chernPart D ε S = 0 := by
  have key : φ.chernPart D ε ≤ (φ.chernPart D ε).restrict Sᶜ := iSup_le fun c => by
    have e : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) S = 0 := by
      rw [chartMeas_apply _ _ hS, (h c).inter_eq, image_empty, Measure.restrict_empty,
        lintegral_zero_measure]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := Sᶜ) (compl_mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ D =>
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) c)
  refine le_antisymm ((key S).trans_eq ?_) zero_le
  rw [Measure.restrict_apply hS, inter_compl_self, measure_empty]

variable [SecondCountableTopology (CxPts p σ)]

theorem chernPart_apply (h : φ.IsCInf) (ε : ℤˣ) (c : AlgChart p σ D) (hS : MeasurableSet S)
    (hc : S ⊆ c.e.source) : φ.chernPart D ε S =
      ∫⁻ v in c.e '' S, ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (c.e.symm v)) := by
  rw [chernPart, glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [c.chernDens_trans c' h hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]) c hS hc,
    chartMeas_apply_of_subset _ _ hS hc]

omit [SecondCountableTopology (CxPts p σ)] in

theorem chernPart_neg_eq_zero (h : φ.IsCInf) (h' : φ.SemiPosReg D) : φ.chernPart D (-1) = 0 := by
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  have := c.chernDens_nonneg h h' (c.e.map_target hv)
  exact ENNReal.ofReal_eq_zero.2 (by simpa using this)

end Weight

namespace Cartier

variable {Z : Scheme.{0}} [IsIntegral Z]

section Ord

variable [IsLocallyNoetherian Z] {D E : CartierDiv Z} {z : Z} {f : Z.functionField}
  {g : Z.functionFieldˣ}

theorem UnitAt.ord_eq_zero (h : UnitAt z f) : Scheme.ord f z = 0 := by
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, ha, rfl⟩ := h
    have : Ring.KrullDimLE 1 (Z.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    exact (Scheme.ord_eq_iff hz (ha.map _).ne_zero).2 (Ring.ordFrac_of_isUnit ha)
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hz f

theorem ord_algebraMap (hz : Order.coheight z = 1) {a : Z.presheaf.stalk z} (ha : a ≠ 0) :
    Scheme.ord (algebraMap _ Z.functionField a) z =
      (Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z ⧸ Ideal.span {a})).toNat := by
  have : Ring.KrullDimLE 1 (Z.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have h0 := mem_nonZeroDivisors_of_ne_zero ha
  refine (Scheme.ord_eq_iff hz ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha)).2 ?_
  exact (Ring.ordFrac_eq_ord _ ha).trans (Ring.ordMonoidWithZeroHom_eq_coe _ h0
    (ENat.coe_toNat (Ring.ord_ne_top h0)).symm)

namespace CartierDiv

def mult (D : CartierDiv Z) (z : Z) : ℤ :=
  Scheme.ord ((D.exists_isEqn z).choose : Z.functionField) z

theorem IsEqn.mult_eq (h : D.IsEqn z g) : D.mult z = Scheme.ord (g : Z.functionField) z := by
  have e := ((h.iff_unitAt).1 (D.exists_isEqn z).choose_spec).ord_eq_zero
  rw [mult, ← div_mul_cancel₀ ((D.exists_isEqn z).choose : Z.functionField) g.ne_zero,
    Scheme.ord_mul (div_ne_zero (Units.ne_zero _) g.ne_zero) g.ne_zero, e, zero_add]

theorem mult_add (D E : CartierDiv Z) (z : Z) : (D + E).mult z = D.mult z + E.mult z := by
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  obtain ⟨g', hg'⟩ := E.exists_isEqn z
  rw [(hg.add hg').mult_eq, hg.mult_eq, hg'.mult_eq, Units.val_mul,
    Scheme.ord_mul g.ne_zero g'.ne_zero]

theorem coheight_eq_one_of_mult_ne_zero (h : D.mult z ≠ 0) : Order.coheight z = 1 :=
  by_contra fun hz => h (Scheme.ord_eq_zero_of_coheight_neq_one hz _)

theorem mem_supp_of_mult_ne_zero (h : D.mult z ≠ 0) : z ∈ D.supp := fun e =>
  h (e.mult_eq.trans (unitAt_one z).ord_eq_zero)

theorem finite_support_mult [CompactSpace Z] (D : CartierDiv Z) :
    (Function.support D.mult).Finite := by
  classical
  have : IsNoetherian Z := {}
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible D.supp.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Z).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := mem_sUnion.1 (hU.le (mem_supp_of_mult_ne_zero hz))
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Z := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Z := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hU.ge (mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [coheight_eq_one_of_mult_ne_zero hz] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

end CartierDiv

end Ord

variable {q : Z ⟶ Sp k} {y : CxPts q σ} {f g : Z.functionField}

abbrev under (y : CxPts q σ) : Z := y.1 (IsLocalRing.closedPoint ℂ)

open Classical in

def ratVal (f : Z.functionField) (y : CxPts q σ) : ℂ :=
  if h : RegAt (under y) f then
    ev q σ h.exists_fnOf.choose h.exists_fnOf.choose_spec.choose_spec.choose y else 0

theorem ratVal_fnOf {U : Z.Opens} (hy : y ∈ ptsIn q σ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    ratVal (fnOf U h a) y = ev q σ U a y := by
  have hr := regAt_fnOf (mem_ptsIn.1 hy) h a
  have e := hr.exists_fnOf.choose_spec.choose_spec.choose_spec
  have hV := mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hr.exists_fnOf.choose_spec.choose, hy⟩
  rw [ratVal, dif_pos hr, ← ev_res inf_le_left hV, ← ev_res inf_le_right hV]
  congr 1
  exact fn_ext fun _ => by rw [fnOf_resG, fnOf_resG, e]

theorem ratVal_mul (hf : RegAt (under y) f) (hg : RegAt (under y) g) :
    ratVal (f * g) y = ratVal f y * ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn q σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_mul,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_mul]

theorem ratVal_ne_zero (hf : UnitAt (under y) f) : ratVal f y ≠ 0 := by
  obtain ⟨U, hU, a, rfl⟩ := hf.regAt.exists_fnOf
  rw [ratVal_fnOf (mem_ptsIn.2 hU)]
  exact (mem_ptsIn_basicOpen (mem_ptsIn.2 hU) a).1 (mem_ptsIn.2 ((unitAt_fnOf_iff hU _ a).1 hf))

variable {L : LB Z} {r : L.ι → Z.functionFieldˣ}

def offSupp (q : Z ⟶ Sp k) (σ : k →+* ℂ) (D : CartierDiv Z) : Set (CxPts q σ) := ptsIn q σ D.supp.compl

theorem isOpen_offSupp (D : CartierDiv Z) : IsOpen (offSupp q σ D) := isOpen_ptsIn _

theorem mem_offSupp {D : CartierDiv Z} : y ∈ offSupp q σ D ↔ under y ∉ D.supp := mem_ptsIn

theorem IsRatSec.unitAt (hL : L.IsLB) (hr : IsRatSec L r)
    (hy : y ∈ offSupp q σ (divOfRatSec hL hr)) {i : L.ι} (hi : y ∈ ptsIn q σ (L.U i)) :
    UnitAt (under y) (r i) :=
  not_not.1 (mt ((presents_divOfRatSec hL hr).isEqn i _ (mem_ptsIn.1 hi)).mem_supp_iff.2
    (mem_offSupp.1 hy))

def logNorm (φ : Weight q σ L) (r : L.ι → Z.functionFieldˣ) (y : CxPts q σ) : ℝ :=
  Real.log ‖ratVal (r (pick φ.isLB y) : Z.functionField) y‖ - φ.φ (pick φ.isLB y) y / 2

theorem logNorm_eq (φ : Weight q σ L) (hr : IsRatSec L r)
    (hy : y ∈ offSupp q σ (divOfRatSec φ.isLB hr)) {i : L.ι} (hi : y ∈ ptsIn q σ (L.U i)) :
    logNorm φ r y = Real.log ‖ratVal (r i : Z.functionField) y‖ - φ.φ i y / 2 := by
  have hj := mem_pick φ.isLB y
  have hij := mem_ptsIn_inf.2 ⟨hi, hj⟩
  have hu := hr.unitAt φ.isLB hy hj
  rw [logNorm, hr i _ (gen_mem (mem_ptsIn.1 hij)),
    ratVal_mul (regAt_fnOf (mem_ptsIn.1 hij) _ _) hu.regAt, ratVal_fnOf hij, φ.trans i _ y hi hj,
    norm_mul, Real.log_mul (norm_ne_zero_iff.2 (ev_ne_zero hij (Units.isUnit _)))
      (norm_ne_zero_iff.2 (ratVal_ne_zero hu)), Real.log_pow, CxPts.gv]
  push_cast
  ring

theorem logNorm_addFn (φ : Weight q σ L) (u : CxPts q σ → ℝ) (r : L.ι → Z.functionFieldˣ)
    (y : CxPts q σ) : logNorm (φ.addFn u) r y = logNorm φ r y - u y / 2 := by
  simp only [logNorm, Weight.addFn]
  ring

theorem exists_isRatSec (hL : L.IsLB) : ∃ r, IsRatSec L r :=
  have ⟨i, hi⟩ := exists_chart hL (genericPoint Z)
  ⟨_, isRatSec_frameRat hL i hi⟩

theorem fnOf_sec_ne_zero {s : L.Sec} (hs : genericPoint Z ∈ nonzeroLocus s) {i : L.ι}
    (h : genericPoint Z ∈ L.U i) : fnOf _ h (s.f i) ≠ 0 :=
  ((unitAt_fnOf_iff h h _).2 ((mem_nonzeroLocus_iff s i h).1 hs)).ne_zero

open Classical in

def ratOfSec (s : L.Sec) (hs : genericPoint Z ∈ nonzeroLocus s) (i : L.ι) :
    Z.functionFieldˣ :=
  if h : genericPoint Z ∈ L.U i then Units.mk0 _ (fnOf_sec_ne_zero hs h) else 1

variable {hL : L.IsLB} {s : L.Sec} {hs : genericPoint Z ∈ nonzeroLocus s}

theorem val_ratOfSec {i : L.ι} (h : genericPoint Z ∈ L.U i) :
    (ratOfSec s hs i : Z.functionField) = fnOf _ h (s.f i) := by
  rw [ratOfSec, dif_pos h, Units.val_mk0]

variable (s hs) in

theorem isRatSec_ratOfSec : IsRatSec L (ratOfSec s hs) := fun i j h => by
  rw [val_ratOfSec h.1, val_ratOfSec h.2, ← fnOf_resG inf_le_left h, ← fnOf_resG inf_le_right h,
    ← map_mul]
  exact congrArg _ (s.compat i j)

variable (hL s hs) in

abbrev divOfSec : CartierDiv Z := divOfRatSec hL (isRatSec_ratOfSec s hs)

theorem notMem_supp_divOfSec {z : Z} : z ∉ (divOfSec hL s hs).supp ↔ z ∈ nonzeroLocus s := by
  obtain ⟨i, hi⟩ := exists_chart hL z
  rw [((presents_divOfRatSec hL _).isEqn i z hi).mem_supp_iff, not_not, val_ratOfSec (gen_mem hi),
    unitAt_fnOf_iff hi, mem_nonzeroLocus_iff s i hi]

theorem offSupp_divOfSec : offSupp q σ (divOfSec hL s hs) = ptsIn q σ (nonzeroLocus s) :=
  Set.ext fun _ => mem_offSupp.trans (notMem_supp_divOfSec.trans mem_ptsIn.symm)

theorem mult_divOfSec [IsLocallyNoetherian Z] {z : Z} (hz : Order.coheight z = 1) {i : L.ι}
    (hi : z ∈ L.U i) : (divOfSec hL s hs).mult z = (Module.length (Z.presheaf.stalk z)
      (Z.presheaf.stalk z ⧸ Ideal.span {Z.presheaf.germ _ z hi (s.f i)})).toNat := by
  have e := algebraMap_germ hi (s.f i)
  rw [((presents_divOfRatSec hL _).isEqn i z hi).mult_eq, val_ratOfSec (gen_mem hi), ← e]
  exact ord_algebraMap hz fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    (e.symm.trans ((congrArg _ h0).trans (map_zero _)))

theorem mult_divOfSec_nonneg [IsLocallyNoetherian Z] (z : Z) : 0 ≤ (divOfSec hL s hs).mult z := by
  by_cases h : (divOfSec hL s hs).mult z = 0
  · exact h.ge
  · obtain ⟨i, hi⟩ := exists_chart hL z
    rw [mult_divOfSec (CartierDiv.coheight_eq_one_of_mult_ne_zero h) hi]
    exact Nat.cast_nonneg _

theorem logNorm_ratOfSec (φ : Weight q σ L) (hy : y ∈ ptsIn q σ (nonzeroLocus s)) :
    logNorm φ (ratOfSec s hs) y = Real.log (φ.nsq (secVal q σ s) y) / 2 := by
  have hi := mem_pick φ.isLB y
  have h0 := (secVal_ne_zero_iff s hi).2 hy
  rw [logNorm, val_ratOfSec (gen_mem (mem_ptsIn.1 hi)), ratVal_fnOf hi, Weight.nsq,
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 h0)) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_pow, secVal_apply]
  push_cast
  ring

theorem IsRatSec.pow_one (hr : IsRatSec L r) : IsRatSec (lbPow L 1) fun j => r (j PUnit.unit) :=
  fun j j' h => by
  have h' : genericPoint Z ∈ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    ⟨mem_iInter.1 h.1 PUnit.unit, mem_iInter.1 h.2 PUnit.unit⟩
  rw [hr _ _ h']
  congr 1
  have e : (lbPow L 1).g j j' = res (X := Z) (U := L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))
      (V := (lbPow L 1).U j ⊓ (lbPow L 1).U j')
      (fun _ hx => ⟨mem_iInter.1 hx.1 PUnit.unit, mem_iInter.1 hx.2 PUnit.unit⟩)
      (L.g (j PUnit.unit) (j' PUnit.unit)) := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_one _).trans ?_)
    rfl
  rw [e]
  exact (fnOf_resG (fun _ hx => ⟨mem_iInter.1 hx.1 PUnit.unit, mem_iInter.1 hx.2 PUnit.unit⟩ :
    (lbPow L 1).U j ⊓ (lbPow L 1).U j' ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) h _).symm

theorem divOfRatSec_pow_one (hL : L.IsLB) (hr : IsRatSec L r) (h : (lbPow L 1).IsLB) :
    divOfRatSec h hr.pow_one = divOfRatSec hL hr := CartierDiv.ext_of_isEqn fun z =>
  have ⟨i, hi⟩ := exists_chart hL z
  ⟨r i, (presents_divOfRatSec h hr.pow_one).isEqn (fun _ => i) z (mem_iInter.2 fun _ => hi),
    (presents_divOfRatSec hL hr).isEqn i z hi⟩

theorem logNorm_pow_one (φ : Weight q σ L) (hr : IsRatSec L r)
    (hy : y ∈ offSupp q σ (divOfRatSec φ.isLB hr)) :
    logNorm (φ.pow 1) (fun j => r (j PUnit.unit)) y = logNorm φ r y := by
  rw [logNorm_eq φ hr hy (mem_pow_iff.1 (mem_pick (φ.pow 1).isLB y)), logNorm]
  exact congrArg (_ - · / 2) ((φ.zpow_φ _ _ y).trans (by simp))

end Cartier

structure IsArithVar (p : X ⟶ Sp k) (D : ℕ) : Prop where

  isDomain : IsDomain k

  finite : Module.Finite ℤ k

  isIntegral : IsIntegral X

  isProjOver : IsProjOver p

  flat : Flat (p ≫ spMap (Int.castRingHom k))

  dim_eq : topologicalKrullDim X = (D + 1 : ℕ)

def GenSmooth (p : X ⟶ Sp k) (D : ℕ) : Prop := ∀ σ : k →+* ℂ, Nonempty (AnRead p σ D)

theorem genSmooth_of_smooth (p : X ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] :
    GenSmooth p D := fun _ => inferInstance

theorem flat_int_iff_charZero [IsIntegral X] (t : X ⟶ Sp ℤ) : Flat t ↔ CharZero Γ(X, ⊤) := by
  have key (U : X.Opens) [Nonempty U] : (t.appLE ⊤ U le_top).hom.Flat ↔ CharZero Γ(X, U) := by
    have e : (t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom =
      algebraMap ℤ Γ(X, U) := RingHom.ext_int _ _
    rw [← RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of ℤ)).inv, e,
      RingHom.flat_algebraMap_iff, Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot, Module.isTorsionFree_int_iff_isAddTorsionFree]
    exact ⟨fun _ => .of_isAddTorsionFree _ Γ(X, U), fun _ => inferInstance⟩
  have res (U : X.Opens) [Nonempty U] : CharZero Γ(X, U) ↔ CharZero Γ(X, ⊤) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (Opens.mem_top (genericPoint X))
    have : Nonempty U := ⟨⟨_, hx⟩⟩
    exact (res U).1 ((key U).1 (HasRingHomProperty.appLE @Flat t h ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _))
  · refine HasRingHomProperty.of_iSup_eq_top (P := @Flat)
      (fun U : {U : X.affineOpens // Nonempty U.1} => U.1) (top_le_iff.1 fun x _ => ?_) fun U => ?_
    · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
      exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, ⟨⟨x, hx⟩⟩⟩, hx⟩
    · have := U.2
      exact (key _).2 ((res _).2 h)

namespace IsArithVar

variable {D : ℕ} (h : IsArithVar p D)
include h

theorem isNoetherianRing : IsNoetherianRing k :=
  have := h.finite
  IsNoetherianRing.of_finite ℤ k

theorem isNoetherian : IsNoetherian X :=
  have := h.isNoetherianRing
  isNoetherian_of_isProjOver h.isProjOver

theorem isLocallyNoetherian : IsLocallyNoetherian X := h.isNoetherian.toIsLocallyNoetherian

theorem charZero : CharZero Γ(X, ⊤) :=
  have := h.isIntegral
  (flat_int_iff_charZero _).1 h.flat

theorem charZero_base : CharZero k :=
  have := h.charZero
  (DVR.FlatBC.algX p ⊤).charZero

theorem finite_emb : Finite (k →+* ℂ) :=
  have := h.finite
  have := h.isDomain
  have := h.charZero_base
  .of_equiv _ (RingHom.equivIntAlgHom k ℂ).symm

theorem compactSpace (σ : k →+* ℂ) : CompactSpace (CxPts p σ) := CxPts.compactSpace σ h.isProjOver

theorem of_isClosedImmersion (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y]
    (hc : CharZero Γ(Y, ⊤)) {e : ℕ} (he : topologicalKrullDim Y = (e + 1 : ℕ)) :
    IsArithVar (i ≫ p) e :=
  have ⟨N, j, _, hj⟩ := h.isProjOver
  ⟨h.1, h.2, ‹_›, ⟨N, i ≫ j, inferInstance, by rw [Category.assoc, hj]⟩,
    (flat_int_iff_charZero _).2 hc, he⟩

end IsArithVar

structure HermLB (p : X ⟶ Sp k) where

  B : LB X

  isLB : B.IsLB

  φ : ∀ σ : k →+* ℂ, Weight p σ B

  cInf : ∀ σ, (φ σ).IsCInf

  conj : ∀ σ σ', (φ σ).IsConj (φ σ')

namespace CxPts

variable {σ' : k →+* ℂ} {y : CxPts p σ} {y' : CxPts p σ'}

theorem eq_conj_of_conj (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    σ' = (starRingEnd ℂ).comp σ := by
  have e : spMap σ' = spMap ((starRingEnd ℂ).comp σ) := by
    rw [← y'.2, h, Category.assoc, y.2, ← Spec.map_comp]
    rfl
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

end CxPts

namespace HermLB

variable (L M : HermLB p)

theorem isSmooth {D : ℕ} (R : AnRead p σ D) : (L.φ σ).IsSmooth R :=
  (Weight.isCInf_iff_isSmooth R).1 (L.cInf σ)

def tens : HermLB p where
  B := CechPic.tens L.B M.B
  isLB := isLB_tens L.isLB M.isLB
  φ σ := (L.φ σ).tens (M.φ σ)
  cInf σ := (L.cInf σ).tens (M.cInf σ)
  conj σ σ' c y y' h hy := congrArg₂ (· + ·) (L.conj σ σ' _ y y' h (mem_ptsIn_inf.1 hy).1)
    (M.conj σ σ' _ y y' h (mem_ptsIn_inf.1 hy).2)

def dual : HermLB p where
  B := CechPic.dual L.B
  isLB := isLB_dual L.isLB
  φ σ := (L.φ σ).dual
  cInf σ := (L.cInf σ).dual
  conj σ σ' c y y' h hy := congrArg (- ·) (L.conj σ σ' _ y y' h hy)

def pow (m : ℕ) : HermLB p where
  B := lbPow L.B m
  isLB := isLB_lbPow L.isLB m
  φ σ := (L.φ σ).pow m
  cInf σ := (L.cInf σ).zpow m
  conj σ σ' c y y' h hy := ((L.φ σ').zpow_φ _ c y').trans
    ((congrArg _ (L.conj σ σ' _ y y' h (mem_pow_iff.1 hy))).trans ((L.φ σ).zpow_φ _ c y).symm)

def pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : HermLB q where
  B := L.B.pull π
  isLB := LB.isLB_pull L.isLB π
  φ σ := (L.φ σ).pull π hπ
  cInf σ := (L.cInf σ).pull π hπ
  conj σ σ' c y y' h hy := ((L.φ σ').pull_φ π hπ c y').trans
    ((L.conj σ σ' _ _ _ ((congrArg (· ≫ π) h).trans (Category.assoc _ _ _))
      (mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ y) (fun _ => rfl) hy PUnit.unit)).trans
      ((L.φ σ).pull_φ π hπ c y).symm)

abbrev restr (i : Y ⟶ X) : HermLB (i ≫ p) := L.pull i rfl

def shift (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : HermLB p where
  B := L.B
  isLB := L.isLB
  φ σ := (L.φ σ).addFn fun _ => 2 * t σ
  cInf σ := (L.cInf σ).addFn (cInfAt_const _)
  conj σ σ' c y y' h hy := congrArg₂ (· + ·) (L.conj σ σ' _ y y' h hy)
    (congrArg (2 * ·) ((congrArg t (eq_conj_of_conj h)).trans (ht σ)))

theorem nsq_shift (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ)
    (s : L.B.ι → CxPts p σ → ℂ) (y : CxPts p σ) :
    ((L.shift t ht).φ σ).nsq s y = (L.φ σ).nsq s y * Real.exp (-(2 * t σ)) :=
  (L.φ σ).nsq_addFn _ s y

variable (p) in

def triv : HermLB p where
  B := LB.triv X
  isLB := LB.isLB_triv X
  φ _ := Weight.ofFun fun _ => 0
  cInf _ := Weight.isCInf_ofFun (cInfAt_const 0)
  conj _ _ _ _ _ _ _ := rfl

variable (p) in

def fs {B : LB X} (hB : B.IsLB) {α : Type} [Fintype α] [DecidableEq α] (b : α → B.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (A : (k →+* ℂ) → Matrix α α ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup α ℂ,
      A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) : HermLB p where
  B := B
  isLB := hB
  φ σ := Weight.fsBasis p σ hB b hb (A σ) (hA σ)
  cInf σ := Weight.isCInf_fsBasis hB b hb _ _
  conj σ σ' i y y' h hy := by
    obtain rfl := eq_conj_of_conj h
    obtain ⟨U, hU, e⟩ := hc σ
    exact Weight.isConj_fsBasis_of_unitary hB b hb (hA σ) (hA _) hU e i y y' h hy

def smallSec : Set L.B.Sec := {s | ∀ σ (y : CxPts p σ), (L.φ σ).nsq (secVal p σ s) y ≤ 1}

theorem zero_mem_smallSec : 0 ∈ L.smallSec := fun σ y => by
  rw [map_zero]
  simp [Weight.nsq]

def SemiPos (D : ℕ) : Prop := ∀ σ, (L.φ σ).SemiPosReg D

variable {L} in

theorem semiPos_iff {D : ℕ} (R : ∀ σ, AnRead p σ D) : L.SemiPos D ↔ ∀ σ, (L.φ σ).SemiPos (R σ) :=
  forall_congr' fun σ => Weight.semiPosReg_iff (L.cInf σ) (R σ)

end HermLB

namespace HermLB

section Sub

variable {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k} (L M : HermLB q)
  {r : M.B.ι → Z.functionFieldˣ}

abbrev div (hr : IsRatSec M.B r) : CartierDiv Z := divOfRatSec M.isLB hr

def ArchIntegrable (e : ℕ) (hr : IsRatSec M.B r) : Prop :=
  ∀ σ, (L.φ σ).ChernIntegrableOn e (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r)

def archInt (e : ℕ) (hr : IsRatSec M.B r) : ℝ :=
  ∑ᶠ σ, (L.φ σ).chernInt e (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r)

def curveDeg [IsLocallyNoetherian Z] (hr : IsRatSec M.B r) : ℝ :=
  ∑ᶠ z, ((M.div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
    ∑ᶠ σ, ∑ᶠ y : CxPts q σ, logNorm (M.φ σ) r y

end Sub

variable (L : HermLB p)

structure IsArithHeight (h : X → ℝ) : Prop where

  vertical : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (d : ℕ), topologicalKrullDim Z = d →
    h (i (genericPoint Z)) = topSelfIntersection κ (L.B.pull i) d * Real.log (Nat.card κ)

  point : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → topologicalKrullDim Z = 1 →
    ∀ (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (L.restr i).B r),
    h (i (genericPoint Z)) = (L.restr i).curveDeg hr

  recursion : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → ∀ e : ℕ, 1 ≤ e →
    topologicalKrullDim Z = (e + 1 : ℕ) → ∀ (m : ℕ)
    (r : ((L.restr i).pow m).B.ι → Z.functionFieldˣ) (hr : IsRatSec ((L.restr i).pow m).B r),
    (L.restr i).ArchIntegrable ((L.restr i).pow m) e hr ∧
    m * h (i (genericPoint Z)) = ∑ᶠ z, ((((L.restr i).pow m).div hr).mult z : ℝ) * h (i z) -
      (L.restr i).archInt ((L.restr i).pow m) e hr

def IsSelfInter [IsIntegral X] (a : ℝ) : Prop :=
  ∃ h, L.IsArithHeight h ∧ h (genericPoint X) = a

structure IsNef (D : ℕ) : Prop where

  semiPos : L.SemiPos D

  vertical : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 →
    0 ≤ topSelfIntersection κ (L.B.pull i) 1

  horizontal : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → topologicalKrullDim Z = 1 →
    ∃ (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (L.restr i).B r),
    0 ≤ (L.restr i).curveDeg hr

variable {L} {h h' : X → ℝ}

theorem IsArithHeight.recursion_one (H : L.IsArithHeight h) {Z : Scheme.{0}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) {e : ℕ}
    (he : 1 ≤ e) (hd : topologicalKrullDim Z = (e + 1 : ℕ))
    {r : (L.restr i).B.ι → Z.functionFieldˣ} (hr : IsRatSec (L.restr i).B r) :
    (L.restr i).ArchIntegrable (L.restr i) e hr ∧
    h (i (genericPoint Z)) = ∑ᶠ z, (((L.restr i).div hr).mult z : ℝ) * h (i z) -
      (L.restr i).archInt (L.restr i) e hr := by
  obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd 1 _ hr.pow_one
  have e₁ : ((L.restr i).pow 1).div hr.pow_one = (L.restr i).div hr := divOfRatSec_pow_one _ hr _
  have e₂ (σ) : EqOn (logNorm (((L.restr i).pow 1).φ σ) fun j => r (j PUnit.unit))
      (logNorm ((L.restr i).φ σ) r) (offSupp _ σ ((L.restr i).div hr)) :=
    fun y hy => logNorm_pow_one _ hr hy
  unfold ArchIntegrable at h₁
  rw [e₁] at h₁
  unfold archInt at h₂
  rw [e₁, Nat.cast_one, one_mul] at h₂
  exact ⟨fun σ => (h₁ σ).congr (isOpen_offSupp _).measurableSet (e₂ σ), h₂.trans (congrArg _
    (finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (e₂ σ)))⟩

theorem IsArithHeight.closedPoint (H : L.IsArithHeight h) {x : X} (hx : IsClosed {x})
    [Finite (X.residueField x)] : h x = Real.log (Nat.card (X.residueField x)) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  let := (Scheme.ΓSpecIso (X.residueField x)).inv.hom.toAlgebra
  have hd : topologicalKrullDim (Spec (X.residueField x)) = (0 : ℕ) :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans (ringKrullDim_eq_zero_of_field _)
  have e := H.vertical _ (X.fromSpecResidueField x) (X.residueField x) 0 hd
  have e₁ : Module.finrank (X.residueField x) Γ(Spec (X.residueField x), ⊤) = 1 :=
    ((AlgEquiv.ofBijective (Algebra.ofId _ _) (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (X.residueField x)).inv)).toLinearEquiv.finrank_eq).symm.trans
      (Module.finrank_self _)
  rw [Scheme.fromSpecResidueField_apply, topSelfIntersection, interNum_of_isEmpty,
    chi_structureModule_of_isAffine, e₁] at e
  simpa using e

end HermLB

theorem exists_isClosedImmersion_genericPoint (x : X) : ∃ (Z : Scheme.{0}) (i : Z ⟶ X)
    (_ : IsClosedImmersion i) (_ : IsIntegral Z), i (genericPoint Z) = x := by
  let C : Closeds X := ⟨closure {x}, isClosed_closure⟩
  have := isIntegral_red (Z := C) isIrreducible_singleton.closure
  refine ⟨_, redι C, inferInstance, this, ?_⟩
  have h₁ := (genericPoint_spec _).image (redι C).continuous
  rw [image_univ, range_redι, C.isClosed.closure_eq] at h₁
  exact h₁.eq isGenericPoint_closure

namespace IsArithVar

variable {D : ℕ} (hX : IsArithVar p D) {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
include hX i

theorem isNoetherian_sub : IsNoetherian Z :=
  have := hX.isNoetherianRing
  have ⟨N, j, _, hj⟩ := hX.isProjOver
  isNoetherian_of_isProjOver (f := i ≫ p) ⟨N, i ≫ j, inferInstance, by rw [Category.assoc, hj]⟩

variable [IsIntegral Z]

theorem exists_dim_eq : ∃ d : ℕ, topologicalKrullDim Z = d := by
  have h₁ : topologicalKrullDim Z ≤ (D + 1 : ℕ) :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hX.dim_eq.le
  have : Nonempty (IrreducibleCloseds Z) := ⟨⟨univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
  have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim Z := Order.krullDim_nonneg
  generalize topologicalKrullDim Z = a at *
  induction a with
  | bot => exact absurd h₂ (by simp)
  | coe a =>
    induction a with
    | top => exact absurd h₁ (by rw [not_le]; exact WithBot.coe_lt_coe.2 (ENat.coe_lt_top _))
    | coe a => exact ⟨a, rfl⟩

theorem dim_ne_zero (hc : CharZero Γ(Z, ⊤)) : topologicalKrullDim Z ≠ 0 := fun h0 => by
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  let t := i ≫ p ≫ spMap (Int.castRingHom k)
  have : Flat t := (flat_int_iff_charZero t).2 hc
  obtain ⟨z, -, hz⟩ := Flat.generalizingMap t (genericPoint_specializes (t (genericPoint Z)))
  have hs : range t = univ := by
    rw [← t.isClosedMap.isClosed_range.closure_eq]
    exact eq_univ_of_univ_subset ((genericPoint_spec (Sp ℤ)).def.ge.trans
      (closure_mono (singleton_subset_iff.2 ⟨z, hz⟩)))
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (eq_univ_of_univ_subset (@this
      ⟨univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (subset_univ _))) (genericPoint_spec Z)
  have hs' := Set.range_eq_univ.1 hs
  obtain ⟨a, ha⟩ := hs' (⊥ : PrimeSpectrum ℤ)
  obtain ⟨b, hb⟩ := hs' (⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2
    Int.prime_two⟩ : PrimeSpectrum ℤ)
  have e := congrArg PrimeSpectrum.asIdeal (hb.symm.trans (((hu b).trans (hu a).symm) ▸ ha))
  exact two_ne_zero (Ideal.span_singleton_eq_bot.1 e)

theorem vertical_or_horizontal :
    (∃ (ℓ : ℕ) (_ : Fact ℓ.Prime), Nonempty (Algebra (ZMod ℓ) Γ(Z, ⊤))) ∨
      (CharZero Γ(Z, ⊤) ∧ ∃ e : ℕ, topologicalKrullDim Z = (e + 1 : ℕ)) := by
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Z, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Z, ⊤) ℓ with hℓ | rfl
  · exact .inl ⟨ℓ, ⟨hℓ⟩, ⟨ZMod.algebra _ ℓ⟩⟩
  · have hc := CharP.charP_to_charZero Γ(Z, ⊤)
    obtain ⟨_ | e, hd⟩ := hX.exists_dim_eq i
    · exact absurd hd (hX.dim_ne_zero i hc)
    · exact .inr ⟨hc, e, hd⟩

end IsArithVar

namespace HermLB

variable {L : HermLB p} {h h' : X → ℝ} {D : ℕ}

theorem IsArithHeight.unique (hX : IsArithVar p D) (H : L.IsArithHeight h)
    (H' : L.IsArithHeight h') : h = h' := by
  have := hX.isNoetherian
  funext x
  induction x using (InvImage.wf (fun x : X => (⟨closure {x}, isClosed_closure⟩ : Closeds X))
    (wellFounded_lt (α := Closeds X))).induction with
  | _ x ih =>
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have := hX.isNoetherian_sub i
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, _ | e, he⟩
  · obtain ⟨d, hd⟩ := hX.exists_dim_eq i
    exact (H.vertical Z i (ZMod ℓ) d hd).trans (H'.vertical Z i (ZMod ℓ) d hd).symm
  · exact (H.point Z i hc he r hr).trans (H'.point Z i hc he r hr).symm
  · rw [(H.recursion_one i hc e.succ_pos he hr).2, (H'.recursion_one i hc e.succ_pos he hr).2]
    refine congrArg (· - _) (finsum_congr fun z => ?_)
    by_cases hz : ((L.restr i).div hr).mult z = 0
    · simp [hz]
    have hs := (genericPoint_specializes z).map i.continuous
    refine congrArg _ (ih _ (lt_of_le_not_ge (closure_minimal (singleton_subset_iff.2
      hs.mem_closure) isClosed_closure) fun hle => ?_))
    have e := i.isClosedEmbedding.injective
      (hs.antisymm (specializes_iff_mem_closure.2 (hle (subset_closure rfl)))).eq
    exact CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hz)

theorem IsSelfInter.unique (hX : IsArithVar p D) [IsIntegral X] {a b : ℝ} (ha : L.IsSelfInter a)
    (hb : L.IsSelfInter b) : a = b := by
  obtain ⟨h, H, rfl⟩ := ha
  obtain ⟨h', H', rfl⟩ := hb
  rw [H.unique hX H']

theorem IsArithHeight.isNef_iff (hX : IsArithVar p D) (H : L.IsArithHeight h) :
    L.IsNef D ↔ L.SemiPos D ∧ ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
      topologicalKrullDim Z = 1 → 0 ≤ h (i (genericPoint Z)) := by
  refine ⟨fun N => ⟨N.1, fun Z i _ _ hd => ?_⟩, fun N => ⟨N.1, fun Z i _ _ κ _ _ _ hd => ?_,
    fun Z i _ _ _ hc hd => ?_⟩⟩
  · have := hX.isNoetherian_sub i
    rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩
    · rw [H.vertical Z i (ZMod ℓ) 1 hd]
      exact mul_nonneg (Int.cast_nonneg (N.vertical Z i _ hd)) (Real.log_natCast_nonneg _)
    · obtain ⟨r, hr, h0⟩ := N.horizontal Z i hc hd
      exact h0.trans_eq (H.point Z i hc hd r hr).symm
  · have h0 := (N.2 Z i hd).trans_eq (H.vertical Z i κ 1 hd)
    have h1 : 0 < Real.log (Nat.card κ) :=
      Real.log_pos (by exact_mod_cast Finite.one_lt_card)
    exact_mod_cast nonneg_of_mul_nonneg_left h0 h1
  · obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
    exact ⟨r, hr, (N.2 Z i hd).trans_eq (H.point Z i hc hd r hr)⟩

end HermLB

theorem Weight.nsq_pull_secPull {B : LB X} (φ : Weight p σ B) {q : Y ⟶ Sp k} (π : Y ⟶ X)
    (hπ : π ≫ p = q) (s : B.Sec) (z : CxPts q σ) :
    (φ.pull π hπ).nsq (secVal q σ (secPull s π)) z =
      φ.nsq (secVal p σ s) (PtsOver.map π hπ _ z) := by
  have hj := mem_pick (φ.pull π hπ).isLB z
  rw [φ.nsq_eq (secVal_mem s) (mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z)
    (fun _ => rfl) hj PUnit.unit)]
  exact congrArg₂ (fun a b => ‖a‖ ^ 2 * Real.exp (-b)) (valR_appLE z.1 π _ hj _)
    (φ.pull_φ π hπ _ z)

theorem IsArithVar.finite_residueField {D : ℕ} (hX : IsArithVar p D) {x : X} (hx : IsClosed {x}) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  have hf : IsFinite (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k)) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ _), IsFinite.SpecMap_iff,
    RingHom.ext_int (Spec.preimage (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k))).hom
      (algebraMap ℤ (X.residueField x)), RingHom.finite_algebraMap] at hf
  have hd : topologicalKrullDim (Spec (X.residueField x)) = 0 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans (ringKrullDim_eq_zero_of_field _)
  obtain ⟨ℓ, _⟩ := CharP.exists (X.residueField x)
  rcases CharP.char_is_prime_or_zero (X.residueField x) ℓ with hℓ | rfl
  · have := Fact.mk hℓ
    let := ZMod.algebra (X.residueField x) ℓ
    have := Module.Finite.of_restrictScalars_finite ℤ (ZMod ℓ) (X.residueField x)
    exact Module.finite_of_finite (ZMod ℓ)
  · exact absurd hd (hX.dim_ne_zero (X.fromSpecResidueField x)
      (((Scheme.ΓSpecIso (X.residueField x)).inv.hom.charZero_iff
        (ConcreteCategory.bijective_of_isIso _).1).1 (CharP.charP_to_charZero _)))

namespace HermLB

variable {L : HermLB p} {h : X → ℝ} {Z : Scheme.{0}} (i : Z ⟶ X) [IsIntegral Z]
  [IsLocallyNoetherian Z] (u : L.B.Sec) (hu : genericPoint Z ∈ nonzeroLocus (secPull u i))

theorem IsArithHeight.recursion_sec (H : L.IsArithHeight h) [IsClosedImmersion i]
    (hc : CharZero Γ(Z, ⊤)) {e : ℕ} (he : 1 ≤ e) (hd : topologicalKrullDim Z = (e + 1 : ℕ)) :
    (∀ σ, ((L.restr i).φ σ).ChernIntegrableOn e (ptsIn _ σ (nonzeroLocus (secPull u i))) fun y =>
      Real.log ((L.φ σ).nsq (secVal p σ u) (PtsOver.map i rfl _ y)) / 2) ∧
    h (i (genericPoint Z)) = ∑ᶠ z, ((divOfSec (L.restr i).isLB _ hu).mult z : ℝ) * h (i z) -
      ∑ᶠ σ, ((L.restr i).φ σ).chernInt e (ptsIn _ σ (nonzeroLocus (secPull u i))) fun y =>
        Real.log ((L.φ σ).nsq (secVal p σ u) (PtsOver.map i rfl _ y)) / 2 := by
  obtain ⟨h₁, h₂⟩ := H.recursion_one i hc he hd (isRatSec_ratOfSec _ hu)
  have e₁ (σ) : offSupp (i ≫ p) σ ((L.restr i).div (isRatSec_ratOfSec _ hu)) = _ := offSupp_divOfSec
  have e₂ (σ) : EqOn (logNorm ((L.restr i).φ σ) (ratOfSec _ hu))
      (fun y => Real.log ((L.φ σ).nsq (secVal p σ u) (PtsOver.map i rfl _ y)) / 2)
      (ptsIn _ σ (nonzeroLocus (secPull u i))) := fun y hy =>
    (logNorm_ratOfSec _ hy).trans (congrArg (Real.log · / 2) ((L.φ σ).nsq_pull_secPull i rfl u y))
  refine ⟨fun σ => (e₁ σ ▸ h₁ σ).congr (isOpen_ptsIn _).measurableSet (e₂ σ),
    h₂.trans (congrArg _ (finsum_congr fun σ => ?_))⟩
  rw [e₁]
  exact Weight.chernInt_congr (isOpen_ptsIn _).measurableSet (e₂ σ)

theorem curveDeg_sec
    (h0 : ∀ σ (y : CxPts (i ≫ p) σ), y ∈ ptsIn _ σ (nonzeroLocus (secPull u i))) :
    (L.restr i).curveDeg (isRatSec_ratOfSec _ hu) =
      ∑ᶠ z, ((divOfSec (L.restr i).isLB _ hu).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
      ∑ᶠ σ, ∑ᶠ y : CxPts (i ≫ p) σ,
        Real.log ((L.φ σ).nsq (secVal p σ u) (PtsOver.map i rfl _ y)) / 2 :=
  congrArg _ (finsum_congr fun σ => finsum_congr fun y => (logNorm_ratOfSec _ (h0 σ y)).trans
    (congrArg (Real.log · / 2) ((L.φ σ).nsq_pull_secPull i rfl u y)))

end HermLB

example (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    c.chernDens (Weight.ofFun fun z => Complex.normSq (c.e z 0)) y = 1 / Real.pi := by
  have e : (fun v => ((Complex.normSq (c.e (c.e.symm v) 0) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v : V 1 => ((Complex.normSq (v 0) : ℝ) : ℂ) :=
    eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv => by
      simp only [c.e.right_inv hv]
  have hg := (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : V 1 →L[ℂ] ℂ).contDiff.contDiffAt (n := 2)
    (x := c.e y)
  have h := ReciprocityTheory.L2DbarEstimates.leviV_normSq_comp hg fun _ => 1
  rw [AlgChart.chernDens, AlgChart.hess]
  erw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]
  simp only [leviV, Finset.univ_unique, Finset.sum_singleton, map_one, mul_one,
    ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt (hg.differentiableAt two_ne_zero),
    ContinuousLinearMap.fderiv] at h
  rw [Matrix.det_unique]
  erw [show cHess 1 (fun v : V 1 => ((Complex.normSq (v 0) : ℝ) : ℂ)) (c.e y) default default = _
    from h]
  simp [ReciprocityTheory.L2DbarEstimates.bas]

namespace Weight

variable {B : LB X} {D : ℕ}

theorem semiPosReg_fsBasis {α : Type} [Fintype α] [DecidableEq α] (hB : B.IsLB) (b : α → B.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (M : Matrix α α ℂ) (hM : M.det ≠ 0) :
    (fsBasis p σ hB b hb M hM).SemiPosReg D := fun i c y hy ξ => by
  let G (a : α) (v : V D) : ℂ := ∑ j, M j a * ev p σ _ ((b j).f i) (c.e.symm v)
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hG (a) : ContDiffAt ℂ 2 (G a) (c.e y) := ContDiffAt.sum fun j _ => contDiffAt_const.mul
    (((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho (c.holo _ ((b j).f i))).contDiffAt
      (ho.mem_nhds (mem_over c.e hy.1 hy.2))).of_le (by norm_cast))
  have e (v : V D) : ∑ a, Complex.normSq (G ((Fintype.equivFin α).symm a) v) = ∑ a, ‖G a v‖ ^ 2 :=
    (Equiv.sum_comp (Fintype.equivFin α).symm fun a => Complex.normSq (G a v)).trans
      (Finset.sum_congr rfl fun a _ => Complex.normSq_eq_norm_sq _)
  have h0 := (noCommonZero_combVal (p := p) (σ := σ) hb hM).sum_pos hy.2
  simp only [combVal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  have := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (u := fun a v => Complex.normSq (G ((Fintype.equivFin α).symm a) v))
    (fun a => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun a => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _))
    (by rw [e]; simp only [G, c.e.left_inv hy.1]; exact h0) ξ
  simp only [e] at this
  simp only [fsBasis_φ]
  exact this

theorem SemiPosReg.addFn_const {φ : Weight p σ B} (h : φ.SemiPosReg D) (t : ℝ) :
    (φ.addFn fun _ => t).SemiPosReg D := fun i c y hy ξ => by
  have e := ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_add_const (fun v => (φ.φ i (c.e.symm v) : ℂ)) t (c.e y)
  have e' := fun a b => congrFun₂ e a b
  simp only [cHess, Matrix.of_apply] at e'
  have := h i c y hy ξ
  simp only [addFn, Complex.ofReal_add, leviV, e'] at this ⊢
  exact this

end Weight

namespace HermLB

variable {D : ℕ}

theorem semiPos_fs {B : LB X} (hB : B.IsLB) {α : Type} [Fintype α] [DecidableEq α] (b : α → B.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (A : (k →+* ℂ) → Matrix α α ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup α ℂ,
      A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) :
    (fs p hB b hb A hA hc).SemiPos D := fun σ => Weight.semiPosReg_fsBasis hB b hb _ (hA σ)

theorem SemiPos.shift {L : HermLB p} (h : L.SemiPos D) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : (L.shift t ht).SemiPos D :=
  fun σ => (h σ).addFn_const _

variable (p D) in

theorem isNef_triv : (triv p).IsNef D where
  semiPos σ i c y _ ξ := (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.Y.cmpb_leviV_const 0 _ ξ)).ge
  vertical Z i _ _ κ _ _ _ _ := (interNum_eq_zero_of_cls_eq_zero κ _
    (fun _ => LB.isLB_pull (LB.isLB_triv X) i) 0
    (by rw [cls_pull (LB.isLB_triv X), cls_triv, map_zero])).ge
  horizontal Z i _ _ _ _ _ := by
    have hr : IsRatSec ((triv p).restr i).B fun _ => 1 := fun a b h => by
      obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
      have := congrArg (fun u : Γ(Z, _)ˣ => fnOf _ h.1 u.val) (((triv p).restr i).isLB.g_self a)
      rw [Units.val_one, map_one] at this
      exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm
    refine ⟨_, hr, le_of_eq (Eq.symm ?_)⟩
    have h₁ (z : Z) : (((triv p).restr i).div hr).mult z = 0 :=
      have ⟨a, ha⟩ := exists_chart ((triv p).restr i).isLB z
      ((presents_divOfRatSec _ hr).isEqn a z ha).mult_eq.trans (unitAt_one z).ord_eq_zero
    have h₂ (σ) (y : CxPts (i ≫ p) σ) : logNorm (((triv p).restr i).φ σ) (fun _ => 1) y = 0 := by
      have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
      rw [map_one, ev_one mem_ptsIn_top] at e
      have e' := ((triv p).φ σ).pull_φ i rfl (pick (((triv p).restr i).φ σ).isLB y) y
      rw [logNorm, Units.val_one, e]
      exact (congrArg (_ - · / 2) e').trans (by simp [triv, Weight.ofFun])
    simp [curveDeg, h₁, h₂]

end HermLB

namespace ProjSpace

variable (k) (N : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem isIntegral_of_isDomain [IsDomain k] : IsIntegral (PSpace k N) := by
  let η : ProjectiveSpectrum (grading k N) := ⟨⊥, Ideal.isPrime_bot, fun h =>
    MvPolynomial.X_ne_zero _ (h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem k N 0)))⟩
  have h : closure {η} = univ := eq_univ_of_forall fun x =>
    (ProjectiveSpectrum.le_iff_mem_closure _ _ x).1 (show ⊥ ≤ x.asHomogeneousIdeal from bot_le)
  have : IrreducibleSpace (PSpace k N) :=
    (irreducibleSpace_def _).2 (show IsIrreducible (univ : Set (ProjectiveSpectrum (grading k N)))
      from h ▸ isIrreducible_singleton.closure)
  have : ∀ i, IsReduced ((chartCover k N).X i) := fun i =>
    inferInstanceAs (IsReduced (Sp (MvPolynomial {j // j ≠ i} k)))
  have : IsReduced (PSpace k N) := IsReduced.of_openCover _ (chartCover k N)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isArithVar_int : IsArithVar (PSpace.str ℤ N) N := by
  have := isIntegral_of_isDomain ℤ N
  have : Smooth (PSpace.str ℤ N) := SmoothOfRelativeDimension.smooth N _
  have hc : ∀ i, topologicalKrullDim (chart ℤ N i : Set (PSpace ℤ N)) = (N + 1 : ℕ) := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (chartι ℤ N i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (opensRange_chartι ℤ N i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} ℤ)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [add_comm]
  refine ⟨inferInstance, inferInstance, ‹_›, ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_,
    le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
      ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))⟩
  · rw [RingHom.ext_int (Int.castRingHom ℤ) (RingHom.id ℤ), spMap, CommRingCat.ofHom_id, Spec.map_id,
      Category.comp_id]
    infer_instance
  · obtain ⟨i, hi⟩ := exists_mem_chart ℤ N x
    exact ⟨_, (chart ℤ N i).isOpen, hi, (hc i).le⟩

def hermitianTwistingSheaf : HermLB (PSpace.str k N) :=
  .fs _ (O1_isLB k N) (coord k N) (iSup_nonzeroLocus_coord k N) (fun _ => 1) (fun _ => by simp)
    fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩

theorem hermitianTwistingSheaf_weight (σ : k →+* ℂ) : (hermitianTwistingSheaf k N).φ σ = ProjAn.fsO1 k σ N := rfl

example : GenSmooth (PSpace.str k N) N ∧ (hermitianTwistingSheaf k N).SemiPos N ∧
    ∀ a, coord k N a ∈ (hermitianTwistingSheaf k N).smallSec := by
  refine ⟨genSmooth_of_smooth _ _, HermLB.semiPos_fs _ _ _ _ _ _, fun a σ y => ?_⟩
  have e (a) : Weight.combVal (PSpace.str k N) σ (coord k N) 1 a = secVal _ σ (coord k N a) := by
    simp [Weight.combVal, Matrix.one_apply]
  refine le_of_le_of_eq ?_ (Weight.sum_nsq_fs (hB := O1_isLB k N) (he := fun a => e a ▸ secVal_mem _)
    (h := Weight.noCommonZero_combVal (iSup_nonzeroLocus_coord k N) (M := 1) (by simp)) y)
  exact le_of_eq_of_le (congrArg (Weight.nsq _ · y) (e a).symm)
    (Finset.single_le_sum (fun b _ => Weight.nsq_nonneg _ _ y) (Finset.mem_univ a))

end ProjSpace

namespace ArithBase

theorem isArithVar_id [IsDomain k] [CharZero k] [Module.Finite ℤ k] (hd : ringKrullDim k = 1) :
    IsArithVar (𝟙 (Sp k)) 0 := by
  have hA : IsAmpleLB (LB.triv (Sp k)) := ⟨LB.isLB_triv _, inferInstance, fun x => by
    obtain ⟨s, hs⟩ := ((isGenerated_triv (Sp k)).pow 1).exists_mem x
    exact ⟨1, le_rfl, s, hs, inf_top_eq (nonzeroLocus s) ▸ isAffineOpen_nonzeroLocus_inf
      (isLB_lbPow (LB.isLB_triv _) 1) s (isAffineOpen_top _)⟩⟩
  exact ⟨‹_›, ‹_›, inferInstance, hA.isProjOver _, (flat_int_iff_charZero _).2
    (((Scheme.ΓSpecIso (.of k)).inv.hom.charZero_iff
      (ConcreteCategory.bijective_of_isIso _).1).1 ‹_›),
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim k).trans hd⟩

theorem isArithVar_int : IsArithVar (𝟙 (Sp ℤ)) 0 :=
  isArithVar_id (IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField)

variable {Z : Scheme.{0}} [IsIntegral Z]

section Product

variable [IsLocallyNoetherian Z] [IsAffine Z] (e : ℤ ≃+* Γ(Z, ⊤))
include e

theorem finsum_ord_prime {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∑ᶠ z, (Scheme.ord (fnOf ⊤ (Opens.mem_top _) (e ℓ)) z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
      Real.log ℓ := by
  have hU := isAffineOpen_top Z
  have : IsPrincipalIdealRing Γ(Z, ⊤) := .of_surjective e e.surjective
  have hπ : Prime (e ℓ) := (MulEquiv.prime_iff e).2 (Nat.prime_iff_prime_int.1 hℓ)
  let P : PrimeSpectrum Γ(Z, ⊤) :=
    ⟨Ideal.span {e ℓ}, (Ideal.span_singleton_prime hπ.ne_zero).2 hπ⟩
  have hP0 : P.asIdeal ≠ ⊥ := mt Ideal.span_singleton_eq_bot.1 hπ.ne_zero
  have hPm : P.asIdeal.IsMaximal := P.isPrime.isMaximal hP0
  let z₀ : Z := hU.fromSpec P
  have hz₀ : hU.primeIdealOf ⟨z₀, trivial⟩ = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  rw [finsum_eq_single _ z₀ fun z hz => ?_]
  · let := TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨z₀, trivial⟩ : (⊤ : Z.Opens))
    have hl : IsLocalization.AtPrime (Z.presheaf.stalk z₀) P.asIdeal := by
      have := hU.isLocalization_stalk ⟨z₀, trivial⟩
      convert this
      exact hz₀.symm
    have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP0
      (Z.presheaf.stalk z₀)
    have hm : IsLocalRing.maximalIdeal (Z.presheaf.stalk z₀) =
        Ideal.span {algebraMap Γ(Z, ⊤) _ (e ℓ)} := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal, Ideal.map_span, image_singleton]
    have hc : Order.coheight z₀ = 1 := by
      have := (ringKrullDim_stalk_eq_coheight z₀).symm.trans
        (IsDiscreteValuationRing.ringKrullDim_eq_one _)
      exact_mod_cast this
    have hi := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm
    have h₁ : Scheme.ord (fnOf ⊤ (Opens.mem_top _) (e ℓ)) z₀ = 1 := by
      rw [← algebraMap_germ (Opens.mem_top z₀)]
      exact (ord_algebraMap hc hi.ne_zero).trans
        (congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (Ring.ord_of_irreducible hi))
    have h₂ : Nat.card (Z.residueField z₀) = ℓ :=
      (Nat.card_congr (((IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
        (Z.presheaf.stalk z₀)).symm.trans (Ideal.quotientEquiv (Ideal.span {(ℓ : ℤ)}) P.asIdeal e
          (by rw [Ideal.map_span, image_singleton]; rfl)).symm).trans
        (Int.quotientSpanNatEquivZMod ℓ)).toEquiv).trans (Nat.card_zmod ℓ)
    rw [h₁, h₂, Int.cast_one, one_mul]
  · let := TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨z, trivial⟩ : (⊤ : Z.Opens))
    have := hU.isLocalization_stalk ⟨z, trivial⟩
    have hn : e ℓ ∉ (hU.primeIdealOf ⟨z, trivial⟩).asIdeal := fun h => hz <|
      (hU.fromSpec_primeIdealOf ⟨z, trivial⟩).symm.trans (congrArg hU.fromSpec (PrimeSpectrum.ext
        (hPm.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
          ((Ideal.span_singleton_le_iff_mem _).2 h)).symm))
    have hu : UnitAt z (fnOf ⊤ (Opens.mem_top _) (e ℓ)) :=
      ⟨_, IsLocalization.map_units (Z.presheaf.stalk z)
        (⟨_, hn⟩ : (hU.primeIdealOf ⟨z, trivial⟩).asIdeal.primeCompl), algebraMap_germ (Opens.mem_top z) _⟩
    rw [hu.ord_eq_zero, Int.cast_zero, zero_mul]

theorem product_formula {q : Z ⟶ Sp ℤ} {σ : ℤ →+* ℂ} (y : CxPts q σ) {f : Z.functionField}
    (hf : f ≠ 0) : UnitAt (under y) f ∧
      ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
        Real.log ‖ratVal f y‖ := by
  let G (f : Z.functionField) : ℝ :=
    ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Z.residueField z))
  have hfin {f : Z.functionField} (hf : f ≠ 0) : (Function.support fun z =>
      (Scheme.ord f z : ℝ) * Real.log (Nat.card (Z.residueField z))).Finite :=
    (CartierDiv.principal (Units.mk0 f hf)).finite_support_mult.subset fun z hz h0 => hz (by
      rw [(CartierDiv.isEqn_principal _ z).mult_eq, Units.val_mk0] at h0
      simp [h0])
  have hG {f g : Z.functionField} (hf : f ≠ 0) (hg : g ≠ 0) : G (f * g) = G f + G g := by
    simp only [G, Scheme.ord_mul hf hg, Int.cast_add, add_mul]
    exact finsum_add_distrib (hfin hf) (hfin hg)
  have hlog {f g : Z.functionField} (hf : UnitAt (under y) f) (hg : UnitAt (under y) g) :
      Real.log ‖ratVal (f * g) y‖ = Real.log ‖ratVal f y‖ + Real.log ‖ratVal g y‖ := by
    rw [ratVal_mul hf.regAt hg.regAt, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hf))
      (norm_ne_zero_iff.2 (ratVal_ne_zero hg))]
  have hev (n : ℤ) : ev q σ ⊤ (e n) y = n := by
    rw [ev_eq mem_ptsIn_top, eq_intCast e, map_intCast]
  have hu {n : ℤ} (hn : n ≠ 0) : UnitAt (under y) (fnOf ⊤ (Opens.mem_top _) (e n)) :=
    (unitAt_fnOf_iff (Opens.mem_top _) _ _).2 (mem_ptsIn.1 ((mem_ptsIn_basicOpen mem_ptsIn_top _).2
      (hev n ▸ Int.cast_ne_zero.2 hn)))
  have hint (n : ℤ) (hn : n ≠ 0) :
      G (fnOf ⊤ (Opens.mem_top _) (e n)) = Real.log ‖ratVal (fnOf ⊤ (Opens.mem_top _) (e n)) y‖ := by
    induction n using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact absurd rfl hn
    | h₂ n h =>
      have (z : Z) : Scheme.ord (fnOf ⊤ (Opens.mem_top _) (e n)) z = 0 :=
        (unitAt_fnOf (U := ⊤) trivial trivial (h.map e).unit).ord_eq_zero
      simp only [G, this]
      rw [ratVal_fnOf mem_ptsIn_top, hev]
      rcases Int.isUnit_iff.1 h with rfl | rfl <;> simp
    | h₃ a π ha hπ ih =>
      have hp : G (fnOf ⊤ (Opens.mem_top _) (e π)) = Real.log ‖ratVal (fnOf ⊤ (Opens.mem_top _) (e π)) y‖ := by
        have h₁ := finsum_ord_prime e (Int.prime_iff_natAbs_prime.1 hπ)
        have h₂ (z : Z) : Scheme.ord (fnOf ⊤ (Opens.mem_top _) (e π)) z =
            Scheme.ord (fnOf ⊤ (Opens.mem_top _) (e π.natAbs)) z := by
          rcases Int.natAbs_eq π with h | h
          · rw [← h]
          · have h₃ := (unitAt_fnOf (U := ⊤) (x := z) trivial trivial (-1)).ord_eq_zero
            have h₄ := hu (Int.natCast_ne_zero.2 (Int.natAbs_ne_zero.2 hπ.ne_zero))
            conv_lhs => rw [h, map_neg, ← neg_one_mul, map_mul]
            refine (Scheme.ord_mul (by simp) h₄.ne_zero).trans ?_
            exact (congrArg (· + _) h₃).trans (zero_add _)
        simp only [G, h₂]
        rw [h₁, ratVal_fnOf mem_ptsIn_top, hev, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
      rw [map_mul, map_mul, hG (hu hπ.ne_zero).ne_zero (hu ha).ne_zero, hlog (hu hπ.ne_zero) (hu ha),
        hp, ih ha]
  have := functionField_isFractionRing_of_isAffineOpen Z ⊤ (isAffineOpen_top Z)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Z, ⊤)) f
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  rw [CartierDiv.algebraMap_top] at hf ⊢
  have hq := (hu ha0).mul (hu hb0).inv
  rw [← div_eq_mul_inv] at hq
  have h₁ := hG hf (hu hb0).ne_zero
  have h₂ := hlog hq (hu hb0)
  rw [div_mul_cancel₀ _ (hu hb0).ne_zero] at h₁ h₂
  exact ⟨hq, by linarith [hint a ha0, hint b hb0]⟩

end Product

variable (i : Z ⟶ Sp ℤ)

theorem mem_asIdeal_iff (n : ℤ) : n ∈ (i (genericPoint Z)).asIdeal ↔ (n : Γ(Z, ⊤)) = 0 := by
  have e : i ⁻¹ᵁ PrimeSpectrum.basicOpen n = Z.basicOpen (n : Γ(Z, ⊤)) := by
    rw [← basicOpen_eq_of_affine (R := .of ℤ) n, Scheme.preimage_basicOpen_top,
      eq_intCast (Scheme.ΓSpecIso (.of ℤ)).inv.hom, map_intCast]
  refine not_iff_not.1 (Iff.trans (b := genericPoint Z ∈ Z.basicOpen (n : Γ(Z, ⊤)))
    (e ▸ Iff.rfl) ?_)
  rw [← unitAt_fnOf_iff (Opens.mem_top _) (Opens.mem_top _), ← ne_eq, ← map_ne_zero_iff _ (fnOf_injective ⊤ (Opens.mem_top _))]
  exact ⟨UnitAt.ne_zero, unitAt_genericPoint⟩

omit [IsIntegral Z] in

theorem surjective_intCast [IsClosedImmersion i] :
    Function.Surjective (Int.castRingHom Γ(Z, ⊤)) := by
  rw [← RingHom.ext_int (i.appTop.hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom) (Int.castRingHom _)]
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine i).2.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of ℤ)).inv).2

def trivShift (t : ℝ) : HermLB (𝟙 (Sp ℤ)) := (HermLB.triv _).shift (fun _ => t) fun _ => rfl

open Classical in

theorem isArithHeight_trivShift (t : ℝ) : (trivShift t).IsArithHeight fun x =>
    if x.asIdeal = ⊥ then t else Real.log (Nat.card (ℤ ⧸ x.asIdeal)) where
  vertical Z i _ _ κ _ _ _ d hd := by
    have := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    have hinj := (algebraMap κ Γ(Z, ⊤)).injective
    have hs : Function.Surjective (Int.castRingHom κ) := fun a =>
      have ⟨n, hn⟩ := surjective_intCast i (algebraMap κ _ a)
      ⟨n, hinj ((map_intCast _ n).trans hn)⟩
    have hb : Function.Bijective (algebraMap κ Γ(Z, ⊤)) := ⟨hinj, fun a =>
      have ⟨n, hn⟩ := surjective_intCast i a
      ⟨n, (map_intCast _ n).trans hn⟩⟩
    have hk : (i (genericPoint Z)).asIdeal = RingHom.ker (Int.castRingHom κ) := Ideal.ext fun n => by
      rw [mem_asIdeal_iff, ← map_intCast (algebraMap κ Γ(Z, ⊤)), map_eq_zero_iff _ hinj]
      rfl
    have h0 : RingHom.ker (Int.castRingHom κ) ≠ ⊥ := fun h =>
      have := Finite.of_injective _ ((RingHom.injective_iff_ker_eq_bot _).2 h)
      not_finite ℤ
    obtain rfl : d = 0 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ Z.isoSpec.hom.homeomorph.isHomeomorph] at hd
      have := hd.symm.trans ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans
        ((ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)).symm.trans (ringKrullDim_eq_zero_of_field κ)))
      exact_mod_cast this
    rw [hk, if_neg h0, Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv, topSelfIntersection,
      interNum_of_isEmpty, chi_structureModule_of_isAffine,
      ← (AlgEquiv.ofBijective (Algebra.ofId _ _) hb).toLinearEquiv.finrank_eq, Module.finrank_self]
    simp
  point Z i _ _ _ hc _ r hr := by
    have := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    let e := RingEquiv.ofBijective (Int.castRingHom Γ(Z, ⊤))
      ⟨Int.cast_injective, surjective_intCast i⟩
    have h0 : (i (genericPoint Z)).asIdeal = ⊥ := eq_bot_iff.2 fun n hn =>
      Int.cast_eq_zero.1 ((mem_asIdeal_iff i n).1 hn)
    let σ := Int.castRingHom ℂ
    let y : CxPts (i ≫ 𝟙 _) σ := ofHom (isAffineOpen_top Z) (σ.comp e.symm) fun a =>
      RingHom.congr_fun (RingHom.ext_int ((σ.comp e.symm.toRingHom).comp
        (DVR.FlatBC.algX (i ≫ 𝟙 _) ⊤)) σ) a
    have hy (y' : CxPts (i ≫ 𝟙 _) σ) : y' = y :=
      Subtype.ext ((cancel_mono (i ≫ 𝟙 _)).1 (y'.2.trans y.2.symm))
    let j := pick (((trivShift t).restr i).φ σ).isLB y
    have hj (z : Z) : (((trivShift t).restr i).div hr).mult z = Scheme.ord (r j : Z.functionField) z :=
      ((presents_divOfRatSec _ hr).isEqn j z (mem_iInter.2 fun _ => trivial)).mult_eq
    have e' : (((trivShift t).restr i).φ σ).φ j y = 0 + 2 * t := ((trivShift t).φ σ).pull_φ i rfl j y
    rw [if_pos h0, HermLB.curveDeg, finsum_eq_single _ σ fun σ' h => absurd (RingHom.ext_int _ _) h,
      finsum_eq_single _ y fun y' h => absurd (hy y') h, logNorm]
    simp only [hj]
    rw [(product_formula e y (r j).ne_zero).2]
    rw [e']
    ring
  recursion Z i _ _ _ _ e he hd := by
    have := hd.ge.trans (i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      isArithVar_int.dim_eq.le)
    norm_cast at this
    omega

theorem isSelfInter_trivShift (t : ℝ) : (trivShift t).IsSelfInter t :=
  ⟨_, isArithHeight_trivShift t, if_pos (Ideal.ext fun n =>
    (mem_asIdeal_iff (𝟙 (Sp ℤ)) n).trans (have := isArithVar_int.charZero; Int.cast_eq_zero))⟩

example {t : ℝ} (ht : t < 0) : ¬ (trivShift t).IsNef 0 := fun h => by
  obtain ⟨f, hf, e⟩ := isSelfInter_trivShift t
  exact (((hf.isNef_iff isArithVar_int).1 h).2 _ (𝟙 _) isArithVar_int.dim_eq).not_gt
    (e.symm ▸ ht)

end ArithBase

end GlobalTheory
