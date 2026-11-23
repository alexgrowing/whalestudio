import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixSmoothInvertibleStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphOn

open Set

def shortCut (ε s : ℝ) : ℝ := Real.smoothTransition ((ε / 2 - s) / (ε / 4))

theorem smoothCutoff_eq_one {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ ε / 4) : shortCut ε s = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by positivity)).2 (by linarith))

theorem smoothCutoff_sq_mul_lt {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : shortCut ε s ^ 2 * s < ε := by
  rcases lt_or_ge s (ε / 2) with h | h
  · have h0 := Real.smoothTransition.nonneg ((ε / 2 - s) / (ε / 4))
    have h1 := Real.smoothTransition.le_one ((ε / 2 - s) / (ε / 4))
    have : shortCut ε s ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    nlinarith
  · have : shortCut ε s = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    rw [this]
    simpa using hε

theorem contDiff_shortCut (ε : ℝ) : ContDiff ℝ ∞ (shortCut ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem dtrans_smul (c c' : AlgChart p σ d) (y : CxPts p σ) (t : ℝ) (ξ : Fin d → ℂ) :
    c.dtrans c' y (t • ξ) = t • c.dtrans c' y ξ := by
  funext b
  simp only [AlgChart.dtrans, WithLp.toLp_smul, ContinuousLinearMap.map_smul_of_tower, Pi.smul_apply]
  rfl

def formIn (a : ChartForm p σ d) (c : AlgChart p σ d) (q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) : ℝ :=
  (((q.2.ofLp ᵥ* matIn a c q.1) ⬝ᵥ star q.2.ofLp : ℂ)).re

theorem contDiffOn_formIn {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) (c : AlgChart p σ d) :
    ContDiffOn ℝ ∞ (formIn a c) (c.e.target ×ˢ (univ : Set (ReciprocityTheory.L2DbarEstimates.V d))) := by
  have hm : ∀ i j, ContDiffOn ℝ ∞ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => matIn a c q.1 i j)
      (c.e.target ×ˢ univ) := fun i j =>
    ((GlobalTheory.T.chart_matrix_smooth_invertible k Y p σ d R a ha c).1 i j).comp contDiffOn_fst fun q hq => hq.1
  have hx : ∀ i, ContDiff ℝ ∞ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => q.2.ofLp i) := fun i =>
    (contDiff_piLp_apply 2).comp contDiff_snd
  have e : formIn a c = fun q => Complex.reCLM
      (∑ j, (∑ i, q.2.ofLp i * matIn a c q.1 i j) * Complex.conjCLE (q.2.ofLp j)) := by
    funext q
    simp [formIn, vecMul, dotProduct]
  rw [e]
  refine Complex.reCLM.contDiff.comp_contDiffOn (ContDiffOn.sum fun j _ => ContDiffOn.mul
    (ContDiffOn.sum fun i _ => ((hx i).contDiffOn).mul (hm i j))
    (Complex.conjCLE.contDiff.comp (hx j)).contDiffOn)

theorem exists_isExph_of_isExphOn_univ : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ)
    [SmoothOfRelativeDimension d p] (R : AnRead p σ d) (a : ChartForm p σ d) (E : ChartMap p σ d) (ε : ℝ),
    IsKaehlerForm R a → 0 < ε → ExphOn.IsExphOn a E Set.univ ε → ∃ E' : ChartMap p σ d, IsExph a E' := by
  intro k _ Y p σ d _ R a E ε ha hε hE
  have hsm : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ (t : ℝ) ξ, a c y (t • ξ) = t ^ 2 * a c y ξ :=
    fun c y hy => (continuous_and_smul ha hy).2
  have hnn : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ, 0 ≤ a c y ξ := by
    intro c y hy ξ
    by_cases h : ξ = 0
    · subst h
      have := hsm c y hy 0 0
      rw [smul_zero, zero_pow two_ne_zero, zero_mul] at this
      rw [this]
    · exact (ha.2 c y hy ξ h).le
  have hshort : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ, a c y (shortCut ε (a c y ξ) • ξ) < ε := by
    intro c y hy ξ
    rw [hsm c y hy]
    exact smoothCutoff_sq_mul_lt hε (hnn c y hy ξ)
  let E' : ChartMap p σ d := fun c y ξ => E c y (shortCut ε (a c y ξ) • ξ)
  have hform : ∀ c : AlgChart p σ d, ∀ q ∈ c.e.target ×ˢ (univ : Set (ReciprocityTheory.L2DbarEstimates.V d)),
      formIn a c q = a c (c.e.symm q.1) q.2.ofLp := by
    intro c q hq
    have := (GlobalTheory.T.chart_matrix_smooth_invertible k Y p σ d R a ha c).2.2 q.1 hq.1 q.2
    rw [formIn, ← this, Complex.ofReal_re]
  let g : AlgChart p σ d → ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d :=
    fun c q => (q.1, shortCut ε (formIn a c q) • q.2)
  have hg : ∀ c, ContDiffOn ℝ ∞ (g c) (c.e.target ×ˢ univ) := fun c =>
    contDiffOn_fst.prodMk (((contDiff_shortCut ε).comp_contDiffOn (contDiffOn_formIn ha c)).smul contDiffOn_snd)
  have hopen : ∀ c : AlgChart p σ d, IsOpen (c.e.target ×ˢ (univ : Set (ReciprocityTheory.L2DbarEstimates.V d))) := fun c =>
    c.e.open_target.prod isOpen_univ
  have hFg : ∀ c, ∀ q ∈ c.e.target ×ˢ univ,
      E c (c.e.symm (g c q).1) (g c q).2.ofLp = E' c (c.e.symm q.1) q.2.ofLp := by
    intro c q hq
    simp only [g, E', WithLp.ofLp_smul, hform c q hq]
  have hgs : ∀ c, ∀ q ∈ c.e.target ×ˢ univ,
      (g c q).1 ∈ c.e.target ∧ a c (c.e.symm (g c q).1) (g c q).2.ofLp < ε := by
    intro c q hq
    refine ⟨hq.1, ?_⟩
    simp only [g, WithLp.ofLp_smul, hform c q hq]
    exact hshort c _ (c.e.map_target hq.1) _
  refine ⟨E', ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro c c' y hy hy' ξ
    simp only [E']
    rw [hE.trans c c' y hy hy', dtrans_smul, ha.trans hy hy' ξ]
  · intro c q hq
    have hFc : ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => E c (c.e.symm q.1) q.2.ofLp) (g c q) :=
      hE.cont c _ (hgs c q hq).1 trivial _ (hgs c q hq).2
    have hgc : ContinuousAt (g c) q := (hg c).continuousOn.continuousAt ((hopen c).mem_nhds hq)
    refine (ContinuousAt.congr (hFc.comp hgc) ?_).continuousWithinAt
    exact eventually_of_mem ((hopen c).mem_nhds hq) fun q' hq' => hFg c q' hq'
  · intro c c' q hq
    have hq0 : q ∈ c.e.target ×ˢ (univ : Set (ReciprocityTheory.L2DbarEstimates.V d)) := ⟨hq.1, trivial⟩
    have hF := hE.smooth c c' _ (hgs c q hq0).1 trivial _ (hgs c q hq0).2 (by rw [hFg c q hq0]; exact hq.2)
    have hgd : ContDiffAt ℝ ∞ (g c) q := (hg c).contDiffAt ((hopen c).mem_nhds hq0)
    refine ((hF.comp q hgd).congr_of_eventuallyEq ?_).contDiffWithinAt
    exact eventually_of_mem ((hopen c).mem_nhds hq0) fun q' hq' => by
      simp only [Function.comp_apply, hFg c q' hq']
  · intro c y hy
    simp only [E', smul_zero]
    exact hE.zero c y hy trivial
  · intro c y hy ξ n
    rw [← hE.jets c y hy trivial ξ n]
    apply Filter.EventuallyEq.iteratedDeriv_eq
    have hc : Continuous fun t : ℝ => t ^ 2 * a c y ξ.ofLp := by fun_prop
    have h0 : (0 : ℝ) ^ 2 * a c y ξ.ofLp < ε / 4 := by
      rw [zero_pow two_ne_zero, zero_mul]
      positivity
    filter_upwards [(hc.tendsto 0).eventually (gt_mem_nhds h0)] with t ht
    simp only [E', hsm c y hy, smoothCutoff_eq_one hε ht.le, one_smul]

end GlobalTheory.ChernReg.ExphOn
