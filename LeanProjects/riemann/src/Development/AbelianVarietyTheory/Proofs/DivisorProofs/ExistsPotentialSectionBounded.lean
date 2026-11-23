import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSecOfNot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRangeComplexUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModelGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModelComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeSmoothModelDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeSmoothModelTangentStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.ArchLim

theorem continuous_nsq_secVal {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B : LB Y}
    (ψ : Weight p σ B) (hψ : ψ.IsCInf) (s : B.Sec) : Continuous (ψ.nsq (secVal p σ s)) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hy := mem_pick ψ.isLB y
  have hO := (isOpen_ptsIn (p := p) (σ := σ) (B.U (pick ψ.isLB y))).mem_nhds hy
  have e : ψ.nsq (secVal p σ s) =ᶠ[𝓝 y] fun z =>
      ‖secVal p σ s (pick ψ.isLB y) z‖ ^ 2 * Real.exp (-ψ.φ (pick ψ.isLB y) z) :=
    Filter.eventually_of_mem hO fun z hz => ψ.nsq_eq (secVal_mem s) hz
  refine ContinuousAt.congr ?_ e.symm
  exact ((((continuousOn_ev _).continuousAt hO).norm.pow 2).mul
    ((hψ _ y hy).continuousAt.neg.rexp))

theorem exists_section_norm_le_one : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (m : ℕ) (sc : (lbPow M.lamB m).Sec) (σ : O.κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr O.s.T.Z) σ)], ∃ (L : LocPot (CxPts (genStr O.s.T.Z) σ)) (sg : CxPts (genStr O.s.T.Z) σ → CxPts (genStr O.s.T.Z) σ → ℂ) (a : ℝ), 0 < a ∧ IsPotential (manifold O.s.T.Z σ).finAtlas L ∧ IsSection (manifold O.s.T.Z σ).finAtlas L sg ∧ (∀ y, normSec L sg y ≤ 1) ∧ ∀ y : CxPts M.q (σ.comp _), normSec L sg (up M.b rfl σ y) ^ 2 = a * (((M.lam 2).pow m).φ _).nsq (secVal M.q _ sc) y := by
  intro D O c M m sc σ _
  have hce : IsClosedEmbedding (up M.b rfl σ) := GlobalTheory.T.closed_subscheme_model_generic_fibre O.s.T.Z M.b rfl σ
  have hoe : IsOpenEmbedding (up M.b rfl σ) := ⟨hce.isEmbedding, GlobalTheory.T.isOpen_range_complex_uniformization D O c M σ⟩
  have hcl : IsClosed (Set.range (up M.b rfl σ)) := hce.isClosed_range
  have hlift := GlobalTheory.T.closed_subscheme_model_complex_points O.s.T.Z M.b rfl σ
  have hP := GlobalTheory.T.closed_subscheme_smooth_model_dimension O.s.T.Z M.b rfl σ hoe hcl hlift (((M.lam 2).pow m).φ (σ.comp _))
    (((M.lam 2).pow m).cInf _)
  have hS := GlobalTheory.T.closed_subscheme_smooth_model_tangent O.s.T.Z M.b rfl σ hoe hcl hlift (((M.lam 2).pow m).φ (σ.comp _)) sc
  set ψ := ((M.lam 2).pow m).φ (σ.comp _) with hψdef
  set P := ClopenPush.pot (up M.b rfl σ) hoe hcl ψ.locPot with hPdef
  set S := ClopenPush.sec (up M.b rfl σ) (ψ.locSec (secVal M.q _ sc)) with hSdef
  haveI : CompactSpace (CxPts M.q (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))) := M.ar.compactSpace _
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_nsq_secVal ψ (((M.lam 2).pow m).cInf _) sc).continuousOn
  have hval : ∀ y, normSec P S (up M.b rfl σ y) = √(ψ.nsq (secVal M.q _ sc) y) := fun y => by
    rw [hPdef, hSdef, ClopenPush.normSec_up]
    exact ψ.norm_mul_exp_eq_sqrt (secVal_mem sc) (mem_pick ψ.isLB y)
  set t := Real.log (√C + 1) with ht
  have hC1 : 0 < √C + 1 := by positivity
  have het : Real.exp (-t) = (√C + 1)⁻¹ := by rw [Real.exp_neg, ht, Real.exp_log hC1]
  let L : LocPot (CxPts (genStr O.s.T.Z) σ) :=
    { U := P.U, isOpen_U := P.isOpen_U, mem_U := P.mem_U, φ := fun x z => P.φ x z + t }
  have hnL : ∀ y, normSec L S y = normSec P S y * Real.exp (-t) := fun y => by
    simp only [normSec, L, neg_add, Real.exp_add, mul_assoc]
  refine ⟨L, S, Real.exp (-(2 * t)), Real.exp_pos _, ⟨fun x j => (hP.1 x j).add contDiffOn_const,
    fun x x' y hy => ?_⟩, ⟨hS.1, fun x x' y hy => ?_⟩, fun y => ?_, fun y => ?_⟩
  · obtain ⟨W, hW, hyW, G, hG, e⟩ := hP.2 x x' y hy
    exact ⟨W, hW, hyW, G, hG, fun z hz => by rw [← e z hz]; simp only [L]; ring⟩
  · have e := hS.2 x x' y hy
    simp only [L, neg_add, Real.exp_add, ← mul_assoc, e]
  · rw [hnL]
    by_cases hy : y ∈ Set.range (up M.b rfl σ)
    · obtain ⟨y₀, rfl⟩ := hy
      rw [hval, het, ← div_eq_mul_inv, div_le_one hC1]
      have h1 : ψ.nsq (secVal M.q _ sc) y₀ ≤ C := by
        have := hC y₀ (Set.mem_univ _)
        rwa [Real.norm_of_nonneg (ψ.nsq_nonneg _ _)] at this
      linarith [Real.sqrt_le_sqrt h1]
    · rw [hPdef, hSdef, ClopenPush.normSec_of_not _ _ _ _ hy, zero_mul]
      exact zero_le_one
  · rw [hnL, hval, mul_pow, Real.sq_sqrt (ψ.nsq_nonneg _ _), ← Real.exp_nat_mul]
    push_cast
    ring_nf

end GlobalTheory.ArchLim

end
