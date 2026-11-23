import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarLocalChartEstimate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcExtensionTraceChernForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockModelPosFrameBound
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.PluriharmonicHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoInvOfIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCurvaturePeriodFormulaStatement
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

namespace GlobalTheory.HodgeChTwo

theorem hodgeGram_of_zero {n g rk : ℕ} {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {B : Fin 0 → Matrix (Fin g) (Fin g) ℤ} (h0 : 0 ≤ n) (hP : GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B)
    {z : Fin n → ℂ} (hz : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram h0 τ₀ B z = (τ₀ z).map (fun c => ((c.im : ℝ) : ℂ)) ∧
      ((τ₀ z).map (fun c => ((c.im : ℝ) : ℂ))).PosDef := by
  have he : GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram h0 τ₀ B z = (τ₀ z).map (fun c => ((c.im : ℝ) : ℂ)) := by
    ext i j; simp [GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod]
  refine ⟨he, ?_⟩
  have hrk : rk = 0 := by
    by_contra hne
    have hg : 0 < g := lt_of_lt_of_le (Nat.pos_of_ne_zero hne) hP.rk_le
    have := hP.toric.diag_pos (i := ⟨⟨0, hg⟩, Nat.pos_of_ne_zero hne⟩)
    simp at this
  subst hrk
  have hsym : ((τ₀ z).map Complex.im).IsSymm := by
    ext i j; simp only [Matrix.transpose_apply, Matrix.map_apply]
    rw [← Matrix.transpose_apply (τ₀ z), (hP.symm z hz).eq]
  let e : {j : Fin g // 0 ≤ j.val} ≃ Fin g := Equiv.subtypeUnivEquiv fun j => Nat.zero_le _
  have hpd : ((τ₀ z).map Complex.im).PosDef := by
    convert Matrix.PosDef.submatrix (hP.abelian z hz) e.symm.injective using 1
    ext i j; simp [e]
  rw [show (τ₀ z).map (fun c => ((c.im : ℝ) : ℂ)) = ((τ₀ z).map Complex.im).map Complex.ofReal by
    rw [Matrix.map_map]; rfl]
  exact (GlobalTheory.IndefiniteRowSideFullHecke.PluriharmonicHolomorphic.posDef_ofReal_iff hsym).2 hpd

theorem sum_chTwo_blockModel {e : ℕ} {ι : Type} [Fintype ι] {μ : ι → ℕ} {ρ : ℝ} {W : Set (Fin e → ℂ)}
    {H : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ} (hρ : 0 < ρ)
    (hB : GlobalTheory.CurvInterp.IsBlockModel ρ W H) (hW : W ∈ 𝓝 0) :
    (∀ τ, MContDiffAt 2 (H τ) 0 ∧ IsUnit (H τ 0).det) ∧
      ∀ ξ₁ η₁ ξ₂ η₂ : Fin e → ℂ, ∑ τ, chTwo (H τ) 0 ξ₁ η₁ ξ₂ η₂ = 0 := by
  obtain ⟨n', k, hk, g, rk, τ₀, B, φ, Q, κ, hP, hφ, hφ0, hφpd, hQ, hcard, hli, hκ, hH⟩ := hB
  have h0W : (0 : Fin e → ℂ) ∈ W := mem_of_mem_nhds hW
  have h0b : (0 : Fin e → ℂ) ∈ Metric.ball (0 : Fin e → ℂ) ρ := Metric.mem_ball_self hρ
  have hk0 : k = 0 := by
    by_contra hne
    have := (hH 0 h0b h0W).1.2 ⟨0, Nat.pos_of_ne_zero hne⟩
    rw [hφ0] at this
    exact this rfl
  subst hk0
  obtain ⟨t, htW, hto, ht0⟩ := mem_nhds_iff.1 hW
  have hWo : IsOpen (Metric.ball (0 : Fin e → ℂ) ρ ∩ t) := Metric.isOpen_ball.inter hto
  have hW0 : (0 : Fin e → ℂ) ∈ Metric.ball (0 : Fin e → ℂ) ρ ∩ t := ⟨h0b, ht0⟩
  have hY : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ ∩ t, _ := fun z hz => hodgeGram_of_zero hk hP (hφpd z hz.1)
  refine GlobalTheory.T.block_curvature_period_formula Q (fun z => τ₀ (φ z)) κ H hWo hW0
    (fun τ i l => (hQ τ i l).mono Set.inter_subset_left)
    (fun i l => (hP.holo i l).comp (hφ.mono Set.inter_subset_left) fun z hz => hφpd z hz.1)
    (fun z hz => hP.symm _ (hφpd z hz.1)) (fun z hz => (hY z hz).2) hcard hli hκ fun z hz => ?_
  obtain ⟨-, h1, h2⟩ := hH z hz.1 (htW hz.2)
  rw [(hY z hz).1] at h1 h2
  exact ⟨h1, h2⟩

theorem sum_chTwo_hodge : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (n : ℕ) (U : Set (V n)) (a : V n → CxFr s.T.Z σ), IsOpen U → HolFam U a → ContinuousOn (fun u => (a u).1) U → ∀ u ∈ U, Inner (a u).1 → ∀ ξ₁ η₁ ξ₂ η₂ : V n, ∑ τ : D.host.E →+* ℂ, chTwo (eigGram (x.hodge σ) a τ) u ξ₁ η₁ ξ₂ η₂ = 0 := by
  intro D A N j S κ s x σ n U a hU hHol hC u hu hin ξ₁ η₁ ξ₂ η₂
  let L : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let β : (Fin n → ℂ) → V n := fun z => u + L.symm z
  have hβ : Continuous β := continuous_const.add L.symm.continuous
  have hβd : Differentiable ℂ β := (differentiable_const u).add L.symm.differentiable
  have hCo : IsOpen (β ⁻¹' U) := hU.preimage hβ
  have h0 : (0 : Fin n → ℂ) ∈ β ⁻¹' U := by simp [β, hu]
  have hHb : HolFam (β ⁻¹' U) (fun z => a (β z)) :=
    ⟨GlobalTheory.LocLift.isHolTo_comp hHol.1 hCo hβd.differentiableOn (fun z hz => hz), fun ρ i V f =>
      (hHol.2 ρ i V f).comp (hβd.differentiableOn.mono fun _ hw => hw.1) fun _ hw => ⟨hw.1, hw.2⟩⟩
  have hCb : ContinuousOn (fun z => (a (β z)).1) (β ⁻¹' U) := hC.comp hβ.continuousOn (fun z hz => hz)
  obtain ⟨ρ, hρ, -, hblk⟩ := GlobalTheory.BdGram.hodgeLocal_all x σ n (β ⁻¹' U) (fun z => a (β z)) hCo h0 hHb hCb
  have hW : {z | Inner (a (β z)).1} ∈ 𝓝 (0 : Fin n → ℂ) := by
    have ho : IsOpen {y : CxPts (genStr s.T.Z) σ | Inner y} := GlobalTheory.ShFam.isOpen_not_liesIn (genBd s.T.Z)
    have hca := hCb.continuousAt (hCo.mem_nhds h0)
    exact hca.preimage_mem_nhds (ho.mem_nhds (by simpa [β] using hin))
  obtain ⟨hreg, hsum⟩ := sum_chTwo_blockModel hρ hblk hW
  have key : ∀ τ, eigGram (x.hodge σ) a τ =
      fun v => eigGram (x.hodge σ) (fun z => a (β z)) τ (L (v - u)) := fun τ => funext fun v => by
    have hv : β (L (v - u)) = v := by simp only [β, L.symm_apply_apply, add_sub_cancel]
    change eigGram (x.hodge σ) a τ v = eigGram (x.hodge σ) a τ (β (L (v - u)))
    rw [hv]
  have hψ : ContDiffAt ℂ 2 (fun v : V n => L (v - u)) u :=
    (L.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hfd : fderiv ℂ (fun v : V n => L (v - u)) u = (L : V n →L[ℂ] (Fin n → ℂ)) :=
    (L.hasFDerivAt.comp u ((hasFDerivAt_id u).sub_const u)).fderiv
  have hcurv : ∀ τ ξ η, curv (eigGram (x.hodge σ) a τ) u ξ η =
      curv (eigGram (x.hodge σ) (fun z => a (β z)) τ) 0 (L ξ) (L η) := by
    intro τ ξ η
    have h0' : L (u - u) = 0 := by rw [sub_self, map_zero]
    have hr1 : MContDiffAt 2 (eigGram (x.hodge σ) (fun z => a (β z)) τ) (L (u - u)) := by
      rw [h0']; exact (hreg τ).1
    have hr2 : IsUnit (eigGram (x.hodge σ) (fun z => a (β z)) τ (L (u - u))).det := by
      rw [h0']; exact (hreg τ).2
    rw [key τ, curv_comp_holo (φ := fun v : V n => L (v - u)) hr1 hr2 hψ, hfd, h0']
    rfl
  have hch : ∀ τ, chTwo (eigGram (x.hodge σ) a τ) u ξ₁ η₁ ξ₂ η₂ =
      chTwo (eigGram (x.hodge σ) (fun z => a (β z)) τ) 0 (L ξ₁) (L η₁) (L ξ₂) (L η₂) := fun τ => by
    simp only [chTwo, GlobalTheory.HermFrame.wedge, hcurv]
  rw [Finset.sum_congr rfl fun τ _ => hch τ]
  exact hsum _ _ _ _

end GlobalTheory.HodgeChTwo
