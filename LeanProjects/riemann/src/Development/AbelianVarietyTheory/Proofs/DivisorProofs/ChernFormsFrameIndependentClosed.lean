import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtCompHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnChernFormOfGramMatrixAtCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDbarChernFormOfGramMatrixEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelChernFormOfGramMatrixEqZeroStatement

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology MeasureTheory
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ChernFrame

theorem chernAt_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {H K : V n → Matrix r r ℂ} {v : V n}
    (h : H =ᶠ[𝓝 v] K) (j : ℕ) : chernAt H v j = chernAt K v j := by
  unfold chernAt chernPoly curvPoly
  simp only [curv_congr h]

theorem delAt_congr {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.del_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem dbarAt_congr {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : dbarAt α v = dbarAt β v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.dbar_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem chern_frame_closed : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} (U : κ → Set M),
    (∀ a, IsOpen (U a)) → (∀ y, ∃ a, y ∈ U a) → ∀ (g : κ → κ → M → Matrix ι ι ℂ),
    (∀ a b i j, A.HolOn (U a ∩ U b) fun y => g a b y i j) → ∀ (G : κ → M → Matrix ι ι ℂ),
    (∀ a i j, A.SmoothOn (U a) fun y => G a y i j) → (∀ a, ∀ y ∈ U a, (G a y).PosDef) →
    (∀ a b, ∀ y ∈ U a ∩ U b, G b y = chg (g a b y) (G a y)) → ∀ (j : ℕ),
    (∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x) ∧
    ∀ P : A.Fld, (∀ a (x : A.Pt), x.pt ∈ U a → P x = (A.chern (G a) j x : GlobalTheory.CxForm.Alt n)) →
      A.IsForm P ∧ A.del P = 0 ∧ A.dbar P = 0 := by
  intro M _ n A ι _ _ κ U hUo hUc g hg G hGs hGp hGt j
  have hop : ∀ i a, IsOpen ((A.e i).target ∩ (A.e i).symm ⁻¹' U a) := fun i a =>
    (A.e i).isOpen_inter_preimage_symm (hUo a)
  have hsm : ∀ i a p q, ContDiffOn ℝ ∞ (fun v => G a ((A.e i).symm v) p q)
      ((A.e i).target ∩ (A.e i).symm ⁻¹' U a) := fun i a p q => hGs a p q i
  have hun : ∀ i a, ∀ v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a, IsUnit (G a ((A.e i).symm v)).det :=
    fun i a v hv => (isUnit_iff_isUnit_det _).1 (hGp a _ hv.2).isUnit
  have hpt : ∀ (x : A.Pt) a, x.pt ∈ U a → x.crd ∈ (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' U a :=
    fun x a ha => ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; exact ha⟩
  have hfr : ∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x := by
    intro a b x ha hb
    have hN : IsOpen ((A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (U a ∩ U b)) :=
      (A.e x.1.1).isOpen_inter_preimage_symm ((hUo a).inter (hUo b))
    have hsym : (A.e x.1.1).symm x.crd = x.pt := x.ch.left_inv x.2
    have hx : x.crd ∈ (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (U a ∩ U b) :=
      ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [hsym]; exact ⟨ha, hb⟩⟩
    have hK : MContDiffAt 2 (fun v => G a ((A.e x.1.1).symm v)) x.crd := fun p q =>
      ((hsm x.1.1 a p q).contDiffAt ((hop x.1.1 a).mem_nhds (hpt x a ha))).of_le (by norm_cast)
    have hKu : IsUnit (G a ((A.e x.1.1).symm x.crd)).det := hun x.1.1 a _ (hpt x a ha)
    have hA : ∀ p q, AnalyticAt ℂ (fun w => g a b ((A.e x.1.1).symm w) p q) x.crd := fun p q =>
      GlobalTheory.SCV.analyticAt_of_differentiableOn (hg a b p q x.1.1) (hN.mem_nhds hx)
    have hAu : IsUnit (g a b ((A.e x.1.1).symm x.crd)).det := by
      rw [hsym]
      have h2 := (isUnit_iff_isUnit_det _).1 (hGp b _ hb).isUnit
      rw [hGt a b x.pt ⟨ha, hb⟩, chg, det_mul, det_mul] at h2
      simpa using isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h2)
    have hev : (fun v => G b ((A.e x.1.1).symm v)) =ᶠ[𝓝 x.crd]
        fun v => chg (g a b ((A.e x.1.1).symm v)) (G a ((A.e x.1.1).symm v)) :=
      Filter.eventually_of_mem (hN.mem_nhds hx) fun v hv => hGt a b _ hv.2
    exact (GlobalTheory.T.chernFormOfGramMatrixAt_holomorphic_frameChange _ _ _ _ hK hKu hA hAu hev j).symm
  refine ⟨hfr, fun P hP => ?_⟩
  have hloc : ∀ i a, ∀ v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a,
      A.loc P i v = (chernAt (fun w => G a ((A.e i).symm w)) v j : Alt n) := by
    intro i a v hv
    rw [HolAtlas.loc, dif_pos hv.1, hP a ⟨(i, (A.e i).symm v), (A.e i).map_target hv.1⟩ hv.2]
    show ((chernAt (fun w => G a ((A.e i).symm w)) ((A.e i) ((A.e i).symm v)) j : Ev n) : Alt n) = _
    rw [(A.e i).right_inv hv.1]
  have hgerm : ∀ i a v, v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a →
      A.loc P i =ᶠ[𝓝 v] fun w => (chernAt (fun w' => G a ((A.e i).symm w')) w j : Alt n) :=
    fun i a v hv => Filter.eventually_of_mem ((hop i a).mem_nhds hv) (hloc i a)
  refine ⟨⟨fun i S => ?_, fun x x' hxx => ?_⟩, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
    obtain ⟨a, ha⟩ := hUc ((A.e i).symm v)
    refine ⟨_, hop i a, ⟨hv, ha⟩, ?_⟩
    refine ((GlobalTheory.T.contDiffOn_chernFormOfGramMatrixAt_coefficients _ _ (hop i a) (hsm i a) (hun i a) j S).mono inter_subset_right).congr fun w hw => ?_
    rw [hloc i a w hw.2]
  · obtain ⟨a, ha⟩ := hUc x.pt
    have ha' : x'.pt ∈ U a := hxx ▸ ha
    rw [hP a x ha, hP a x' ha']
    have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      x.ch.isOpen_inter_preimage_symm x'.ch.open_source
    have hxW : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
      ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; show x.pt ∈ _; rw [hxx]; exact x'.2⟩
    have hφ : AnalyticAt ℂ (x'.ch ∘ x.ch.symm) x.crd := GlobalTheory.SCV.analyticAt_of_differentiableOn (A.holo x.1.1 x'.1.1) (hW.mem_nhds hxW)
    have hφv : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
      simp only [Function.comp_apply]; rw [x.ch.left_inv x.2]; show x'.ch x.pt = x'.ch x'.pt; rw [hxx]
    have hH2 : MContDiffAt 2 (fun v => G a (x'.ch.symm v)) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hφv]
      exact fun p q => ((hsm x'.1.1 a p q).contDiffAt ((hop x'.1.1 a).mem_nhds (hpt x' a ha'))).of_le
        (by norm_cast)
    have hHu : IsUnit (G a (x'.ch.symm ((x'.ch ∘ x.ch.symm) x.crd))).det := by
      rw [hφv]; exact hun x'.1.1 a _ (hpt x' a ha')
    have key := GlobalTheory.T.chernFormOfGramMatrixAt_comp_holomorphic (fun v => G a (x'.ch.symm v)) (x'.ch ∘ x.ch.symm) x.crd hφ hH2 hHu j
    rw [hφv] at key
    have hge : (fun v => G a (x.ch.symm v)) =ᶠ[𝓝 x.crd] fun w => G a (x'.ch.symm ((x'.ch ∘ x.ch.symm) w)) :=
      Filter.eventually_of_mem (hW.mem_nhds hxW) fun w hw => by
        simp only [Function.comp_apply]; rw [x'.ch.left_inv hw.2]
    show ((chernAt (fun v => G a (x.ch.symm v)) x.crd j : Ev n) : Alt n) = _
    rw [chernAt_congr hge j, key]
    rfl
  · funext x
    obtain ⟨a, ha⟩ := hUc x.pt
    show delAt (A.loc P x.1.1) x.crd = 0
    rw [delAt_congr (hgerm _ a _ (hpt x a ha))]
    exact GlobalTheory.T.holomorphicDel_chernFormOfGramMatrix_eq_zero _ _ (hop _ a) (hsm _ a) (hun _ a) j _ (hpt x a ha)
  · funext x
    obtain ⟨a, ha⟩ := hUc x.pt
    show dbarAt (A.loc P x.1.1) x.crd = 0
    rw [dbarAt_congr (hgerm _ a _ (hpt x a ha))]
    exact GlobalTheory.T.antiholomorphicDbar_chernFormOfGramMatrix_eq_zero _ _ (hop _ a) (hsm _ a) (hun _ a) j _ (hpt x a ha)

end GlobalTheory.ChernFrame
