import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSncAdaptedCoordinatesOfMemNhdsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotInSncBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

theorem exists_sncChart_isEqn_affine : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∀ y₀ : Y, ∃ (W : Y.Opens) (hW : y₀ ∈ W) (z : Fin n → Γ(Y, W)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ) (e : Y.functionFieldˣ) (f : ι → Γ(Y, W)), IsFrame (dOn q z) ∧ (∀ y ∈ W, A.IsEqn y e) ∧ (∀ i, fnOf W (gen_mem hW) (f i) = s i * e) ∧ ∀ (y : Y) (hy : y ∈ W), ∃ J : Finset (Fin n), IsSncChart q n B y W hy z J w u ∧ ∀ j ∈ J, y ∉ Y.basicOpen (z j) := by
  intro Y _ _ q n _ B hB A ι s hs y₀
  obtain ⟨U, hy₀, z, J, w, u, hc⟩ := GlobalTheory.T.exists_snc_chart ℂ Y q n B hB y₀
  have hgen : genericPoint Y ∉ B := GlobalTheory.PairStep.genericPoint_notMem_of_snc Y B hB
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.T.isSncAdaptedCoordinates_of_mem_nhds Y q n B y₀ U hy₀ z J w u hgen hc
  obtain ⟨N, hyN, e, he⟩ := A.exists_isEqn_nhds y₀
  obtain ⟨W, hWa, hyW, hWle⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y₀ ∈ U ⊓ V ⊓ N from ⟨⟨hy₀, hyV⟩, hyN⟩)
  have hWU : W ≤ U := hWle.trans (inf_le_left.trans inf_le_left)
  have hWV : W ≤ V := hWle.trans (inf_le_left.trans inf_le_right)
  have hWN : W ≤ N := hWle.trans inf_le_right
  have hf : ∀ i, ∃ a : Γ(Y, W), fnOf W (gen_mem hyW) a = s i * e := fun i =>
    exists_fnOf_eq (gen_mem hyW) fun x hx =>
      (he x (hWN hx)).regularAt_iff.1 (CartierDiv.mem_sections.1 (hs i) x)
  choose f hf using hf
  have hfr : IsFrame (dOn q fun j => resG Y hWU (z j)) := by
    have := hc.frame.res hWa hWU
    rwa [resForm_dOn] at this
  refine ⟨W, hyW, fun j => resG Y hWU (z j), w, u, e, f, hfr, fun y hy => he y (hWN hy), hf, ?_⟩
  intro y hy
  obtain ⟨hyU, J', -, hc', hJ'⟩ := hV y (hWV hy)
  refine ⟨J', ⟨hfr, ?_, hc'.spec, hc'.coheight, hc'.inj, hc'.ord_self, hc'.ord_other, hc'.mem⟩, ?_⟩
  · intro j hj
    rw [hc'.val j hj, fnOf_resG]
  · intro j hj hmem
    have hb : Y.basicOpen (resG Y hWU (z j)) = W ⊓ Y.basicOpen (z j) :=
      Y.basicOpen_res (z j) (homOfLE hWU).op
    rw [hb] at hmem
    exact hJ' j hj hmem.2

end GlobalTheory.PairStep
