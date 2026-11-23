import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.MixDens

theorem chern_bc_cell : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (E : ι → B.Modules) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (c : AlgChart q σ 1) (cE : ∀ a, Chart (E a) (r a)) (c' : AlgChart p σ (d + 1)), IsCell e π w c c' → (∀ a, IsCellFrame e π w c' a (h a) (fl a) (cE a)) → ∀ y ∈ c'.e.source, (∀ z : Σ a, Fin (r a), chernMat ((VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)).φ σ) c' y = cHess (d + 1) (fun v => (rootWt e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) z v : ℂ)) (c'.e y)) ∧ ∀ a, flagMat ((h a).pull π w) (fl a) σ c' y = ∑ i, formMat (extTrace (stepGram e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) a i) (c'.e y)) := by
  intro k _ B Y q p π w ι _ r d e σ E h H fl c cE c' hc hcf y hy

  have key : ∀ (a : ι) (i : Fin (r a)) (ac : GlobalTheory.VBExt.AdaptedChart (VMetric.stepSeq (fl a) i) i 1),
      (∀ y ∈ c'.e.source, y ∈ ptsIn p σ ac.U ∧
        ((((h a).pull π w).stepMet (fl a) i).met σ).gram ac.frame y =
          (chg (uni (fib e (c'.e y) a)) (((h a).met σ).G (cE a) (PtsOver.map π w (spMap σ) y))).submatrix
            (emb i) (emb i)) →
      ∀ v ∈ c'.e.target, ((((h a).pull π w).stepMet (fl a) i).met σ).gram ac.frame (c'.e.symm v) =
        stepGram e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) a i v := by
    intro a i ac hac v hv
    have hy' := c'.e.map_target hv
    have hb : c.e.symm (base e v) = PtsOver.map π w (spMap σ) (c'.e.symm v) := by
      have h1 := hc.2.2 _ hy'
      rw [c'.e.right_inv hv] at h1
      have h2 := hy'
      rw [hc.1] at h2
      rw [h1, c.e.left_inv h2.1]
    rw [(hac _ hy').2, c'.e.right_inv hv, stepGram, hb]
  refine ⟨fun z => ?_, fun a => ?_⟩
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
      extTrace_congr (K' := stepGram e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) a i)
        (eventually_of_mem (c'.e.open_target.mem_nhds (c'.e.map_source hy)) (key a i ac hac))]

end GlobalTheory.MixDens
