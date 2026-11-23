import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtFubiniStudyLogSumWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLogSumWeightUniformlyBoundedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem nu_conjPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    {f : X.functionField} (hf : f ∈ P.H a b) {σ σ' : k →+* ℂ} {y : CxPts p σ} {y' : CxPts p σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : P.nu a b σ' y' f = P.nu a b σ y f := by
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  have hi' := CxPts.mem_ptsIn_conj h hi
  have hj' := CxPts.mem_ptsIn_conj h hj
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [GlobalTheory.VolBr.nu_eq k X p P a b f hf σ' y' _ _ hi' hj', GlobalTheory.VolBr.nu_eq k X p P a b f hf σ y _ _ hi hj,
    ratVal_conj h hreg, Complex.norm_conj, P.L.conj σ σ' _ y y' h hi, P.A.conj σ σ' _ y y' h hj]

theorem exists_isCan_bdd : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∃ u : SmFn p, IsCan P e n x u ∧ ∀ σ y, |u.u σ y| ≤ B := by
  intro k _ X _ p D hX P e x hx
  obtain ⟨B, hB, hb⟩ := GlobalTheory.T.fubiniStudy_log_sum_weight_uniformly_bounded k X p D hX P e x hx
  refine ⟨B, hB, fun n hn => ⟨⟨fun σ y => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)),
    fun σ y => GlobalTheory.T.complexPointsSmoothAt_fubiniStudy_log_sum_weight k X p P D e x hx n hn σ y, fun σ σ' i y y' h _ => ?_⟩, fun σ y => rfl, fun σ y => hb n hn σ y⟩⟩
  change ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ' y' (x l) ^ (2 * n)) =
    ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))
  simp only [nu_conjPt P _ _ (hx.mem _) h]

end GlobalTheory.HSAmp
