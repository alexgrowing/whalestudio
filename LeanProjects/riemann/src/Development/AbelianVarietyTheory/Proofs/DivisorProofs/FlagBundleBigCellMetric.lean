import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigCell

open ReciprocityTheory.L2DbarEstimates (bas) in

theorem cHess_comp_base {ι : Type} [Fintype ι] {r : ι → ℕ} {n D : ℕ} (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a)))
    (g : V n → ℂ) (v : V D) (hg : ContDiffAt ℝ 2 g (BigCell.base ε v)) :
    cHess D (g ∘ BigCell.base ε) v = BigCell.blk ε (cHess n g (BigCell.base ε v)) 0 := by
  ext j l
  have hb : ∀ (j : Fin D) (b : Fin n), (BigCell.base ε (bas D j)) b = if ε j = .inl b then 1 else 0 := by
    intro j b
    have : ε.symm (.inl b) = j ↔ ε j = .inl b := by rw [Equiv.symm_apply_eq, eq_comm]
    simp [BigCell.base, bas, this]
  have := GlobalTheory.HessPull.cHess_comp_apply D n g (baseL ε) Set.univ isOpen_univ v trivial
    (baseL ε).contDiff.contDiffOn hg j l
  rw [ContinuousLinearMap.fderiv] at this
  refine this.trans ?_
  simp only [hb, BigCell.blk, submatrix_apply, baseL_apply]
  cases ε j <;> cases ε l <;> simp [diagonal_apply, apply_ite (starRingEnd ℂ)]

theorem chern_bc_cell : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (σ : k →+* ℂ) (E : ι → B.Modules) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (c : AlgChart q σ n) (cE : ∀ a, Chart (E a) (r a)) (c' : AlgChart p σ D), BigCell.IsCell ε π w c c' → (∀ a, BigCell.IsCellFrame ε π w c' a (h a) (fl a) (cE a)) → ∀ y ∈ c'.e.source, (∀ z : Σ a, Fin (r a), chernMat ((VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)).φ σ) c' y = cHess D (fun v => (BigCell.rootWt ε (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) z v : ℂ)) (c'.e y)) ∧ (∀ a, flagMat ((h a).pull π w) (fl a) σ c' y = ∑ i, formMat (extTrace (BigCell.stepGram ε (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) a i) (c'.e y))) ∧ ∀ A : HermLB q, chernMat ((A.pull π w).φ σ) c' y = BigCell.blk ε (chernMat (A.φ σ) c (PtsOver.map π w (spMap σ) y)) 0 := by
  intro k _ B Y q p π w ι _ r n D e σ E h H fl c cE c' hc hcf y hy
  have hbase : ∀ v ∈ c'.e.target, c.e.symm (BigCell.base e v) = PtsOver.map π w (spMap σ) (c'.e.symm v) := by
    intro v hv
    have hy' := c'.e.map_target hv
    have h1 := hc.2.2 _ hy'
    rw [c'.e.right_inv hv] at h1
    have h2 := hy'
    rw [hc.1] at h2
    rw [h1, c.e.left_inv h2.1]

  have key : ∀ (a : ι) (i : Fin (r a)) (ac : GlobalTheory.VBExt.AdaptedChart (VMetric.stepSeq (fl a) i) i 1),
      (∀ y ∈ c'.e.source, y ∈ ptsIn p σ ac.U ∧
        ((((h a).pull π w).stepMet (fl a) i).met σ).gram ac.frame y =
          (chg (uni (BigCell.fib e (c'.e y) a)) (((h a).met σ).G (cE a) (PtsOver.map π w (spMap σ) y))).submatrix
            (emb i) (emb i)) →
      ∀ v ∈ c'.e.target, ((((h a).pull π w).stepMet (fl a) i).met σ).gram ac.frame (c'.e.symm v) =
        BigCell.stepGram e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) a i v := by
    intro a i ac hac v hv
    rw [(hac _ (c'.e.map_target hv)).2, c'.e.right_inv hv, BigCell.stepGram, hbase v hv]
  refine ⟨fun z => ?_, fun a => ?_, fun A => ?_⟩
  · obtain ⟨ac, hac⟩ := hcf z.1 z.2
    have hU := (hac y hy).1
    rw [chernMat, c'.hess_eq (((VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w))).cInf σ) hy
      (i := ac.quot) hU (mem_pick _ y)]
    unfold AlgChart.hess
    refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hy)] with v hv
    congr 1
    show -Real.log _ = -Real.log _
    rw [← key z.1 z.2 ac hac v hv]
    exact congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => -Real.log M.det.re)
      (Met.quot_G _ (VMetric.stepSeq_shortExact _ _) ((fl z.1).isVB z.2.castSucc) ((fl z.1).isVB_gr z.2) ac (hac _ (c'.e.map_target hv)).1)
  · rw [flagMat]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨ac, hac⟩ := hcf a i
    rw [bcMat, Met.bcForm_eq (h := (((h a).pull π w).stepMet (fl a) i).met σ) (VMetric.stepSeq_shortExact _ i) ac _ c'
      (((H a).pull π w).restrict _ _ σ) hy (hac y hy).1 (Met.exists_adapted (VMetric.stepSeq_shortExact _ i) ((fl a).isVB i.castSucc) ((fl a).isVB_gr i) y).choose_spec, Met.bcForm,
      extTrace_congr (K' := BigCell.stepGram e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) a i)
        (eventually_of_mem (c'.e.open_target.mem_nhds (c'.e.map_source hy)) (key a i ac hac))]
  · set m := PtsOver.map π w (spMap σ) with hmdef
    have hy' : m y ∈ c.e.source := by
      have h2 := hy
      rw [hc.1] at h2
      exact h2.1
    set i := pick ((A.pull π w).φ σ).isLB y
    have hi : y ∈ ptsIn p σ ((A.pull π w).B.U i) := mem_pick _ y
    have him : m y ∈ ptsIn q σ (A.B.U (i PUnit.unit)) :=
      mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
    set g : V n → ℂ := fun v => ((A.φ σ).φ (i PUnit.unit) (c.e.symm v) : ℂ)
    have hFy : BigCell.base e (c'.e y) = c.e (m y) := hc.2.2 y hy
    have hg : ContDiffAt ℝ 2 g (BigCell.base e (c'.e y)) := hFy ▸
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((A.cInf σ).contDiffAt c hy' him)
    have e' : (fun v => (((A.pull π w).φ σ).φ i (c'.e.symm v) : ℂ)) =ᶠ[𝓝 (c'.e y)] g ∘ BigCell.base e := by
      filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hy)] with v hv
      have := Weight.pull_φ (A.φ σ) π w i (c'.e.symm v)
      simp only [g, Function.comp_apply, hbase v hv]
      exact congrArg _ this
    rw [chernMat, chernMat, c.hess_eq (A.cInf σ) hy' (i := i PUnit.unit) him (mem_pick _ _)]
    show cHess D _ (c'.e y) = _
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e', cHess_comp_base e g _ hg, hFy]
    rfl

end GlobalTheory.BigCell
