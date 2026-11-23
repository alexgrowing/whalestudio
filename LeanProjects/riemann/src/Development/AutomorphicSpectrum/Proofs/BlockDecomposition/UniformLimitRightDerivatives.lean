import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDerivativeSystemSmoothStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.LimSmooth

theorem tendstoLocallyUniformlyOn_frame {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] {A : ι → Mat n → CLof (Mat n) ℝ} (hA : ∀ p, ContinuousOn (A p) (GLs n))
    {u : ι → ℕ → Mat n → V} {U : ι → Mat n → V}
    (hu : ∀ p, TendstoUniformlyOn (u p) (U p) atTop (GLs n)) :
    TendstoLocallyUniformlyOn
      (fun (k : ℕ) (z : Mat n) => (∑ p, (A p z).smulRight (u p k z) : CLof (Mat n) V))
      (fun z => (∑ p, (A p z).smulRight (U p z) : CLof (Mat n) V)) atTop (GLs n) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  set M : ℝ := ∑ p, (‖A p x‖ + 1) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun p _ => by positivity
  have hnear : ∀ᶠ y in 𝓝[GLs n] x, ∀ p, ‖A p y‖ < ‖A p x‖ + 1 := by
    rw [Filter.eventually_all]
    intro p
    exact Filter.Tendsto.eventually_lt_const (lt_add_one _) (hA p x hx).norm
  have hpos : 0 < ε / (M + 1) := by positivity
  refine ⟨{y | ∀ p, ‖A p y‖ < ‖A p x‖ + 1} ∩ GLs n,
    Filter.inter_mem hnear self_mem_nhdsWithin, ?_⟩
  have hev : ∀ᶠ k in atTop, ∀ p, ∀ y ∈ GLs n, dist (U p y) (u p k y) < ε / (M + 1) := by
    rw [Filter.eventually_all]
    intro p
    exact Metric.tendstoUniformlyOn_iff.1 (hu p) _ hpos
  filter_upwards [hev] with k hk y hy
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  have hterm : ∀ p, ‖(A p y).smulRight (U p y) - (A p y).smulRight (u p k y)‖
      ≤ (‖A p x‖ + 1) * (ε / (M + 1)) := by
    intro p
    have he : (A p y).smulRight (U p y) - (A p y).smulRight (u p k y)
        = (A p y).smulRight (U p y - u p k y) := by
      ext v
      simp [smul_sub]
    rw [he, ContinuousLinearMap.norm_smulRight_apply]
    have h1 := hk p y hy.2
    rw [dist_eq_norm] at h1
    exact mul_le_mul (hy.1 p).le h1.le (norm_nonneg _) (by positivity)
  calc _ ≤ ∑ p, ‖(A p y).smulRight (U p y) - (A p y).smulRight (u p k y)‖ := norm_sum_le _ _
    _ ≤ ∑ p, (‖A p x‖ + 1) * (ε / (M + 1)) := Finset.sum_le_sum fun p _ => hterm p
    _ = M * (ε / (M + 1)) := by rw [Finset.sum_mul]
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

theorem sum_smulRight_apply {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] (B : ι → CLof (Mat n) ℝ) (c : ι → V) (v : Mat n) :
    (∑ q, (B q).smulRight (c q) : CLof (Mat n) V) v = ∑ q, B q v • c q := by
  simp

theorem limit_smooth : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (g : ℕ → Mat n → V), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) →
    (∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n)) →
    ∃ Gf : List (Bool × Fin n × Fin n) → Mat n → V,
      (∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n)) ∧
      ContDiffOn ℝ ∞ (Gf []) (GLs n) ∧ ∀ w, ∀ z ∈ GLs n, Rw w (Gf []) z = Gf w z := by
  intro n V _ _ _ g hg hc
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.derivative_right_basis_expansion n
  have hopen : IsOpen (GLs n) := isOpen_GLs
  let Gf : List (Bool × Fin n × Fin n) → Mat n → V :=
    fun w z => limUnder atTop (fun k => Rw w (g k) z)
  have hpt : ∀ w, ∀ z ∈ GLs n, Tendsto (fun k => Rw w (g k) z) atTop (𝓝 (Gf w z)) := by
    intro w z hz
    have hcs : CauchySeq (fun k => Rw w (g k) z) := (hc w).cauchy_map hz
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
    have he : Gf w z = x := hx.limUnder_eq
    rwa [he]
  have hu : ∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n) := fun w =>
    (hc w).tendstoUniformlyOn_of_tendsto (hpt w)
  have hsm : ∀ k w, ContDiffOn ℝ ∞ (Rw w (g k)) (GLs n) := fun k w =>
    GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg k) w
  have hderiv : ∀ k w, ∀ z ∈ GLs n, fderiv ℝ (Rw w (g k)) z
      = (∑ p, (A p z).smulRight (Rw (p :: w) (g k) z) : CLof (Mat n) V) := by
    intro k w z hz
    exact hA V (fderiv ℝ (Rw w (g k)) z) z hz
  have hhas : ∀ w, ∀ z ∈ GLs n, HasFDerivAt (Gf w)
      (∑ p, (A p z).smulRight (Gf (p :: w) z) : CLof (Mat n) V) z := by
    intro w z hz
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn (f := fun k => Rw w (g k))
      (f' := fun (k : ℕ) (y : Mat n) =>
        (∑ p, (A p y).smulRight (Rw (p :: w) (g k) y) : CLof (Mat n) V))
      (g' := fun y => (∑ p, (A p y).smulRight (Gf (p :: w) y) : CLof (Mat n) V))
      hopen (tendstoLocallyUniformlyOn_frame (u := fun p k => Rw (p :: w) (g k))
        (U := fun p => Gf (p :: w)) (fun p => hAc p |>.continuousOn) (fun p => hu (p :: w)))
      ?_ (hpt w) hz
    intro k y hy
    have hd : DifferentiableAt ℝ (Rw w (g k)) y :=
      ((hsm k w).contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)
    have h2 := hd.hasFDerivAt
    rwa [hderiv k w y hy] at h2
  have hRd : ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Gf w) z = Gf (p :: w) z := by
    intro w p z hz
    have h1 : Rd (bs p) (Gf w) z
        = (∑ q, (A q z).smulRight (Gf (q :: w) z) : CLof (Mat n) V) (z * bs p) := by
      have h0 := (hhas w z hz).fderiv
      exact congrArg (fun L : CLof (Mat n) V => L (z * bs p)) h0
    have h2 : Tendsto (fun k => Rw (p :: w) (g k) z) atTop
        (𝓝 ((∑ q, (A q z).smulRight (Gf (q :: w) z) : CLof (Mat n) V) (z * bs p))) := by
      have h3 : ∀ k, Rw (p :: w) (g k) z
          = ∑ q, (A q z (z * bs p)) • Rw (q :: w) (g k) z := by
        intro k
        have h4 : Rw (p :: w) (g k) z
            = (∑ q, (A q z).smulRight (Rw (q :: w) (g k) z) : CLof (Mat n) V) (z * bs p) :=
          congrArg (fun L : CLof (Mat n) V => L (z * bs p)) (hderiv k w z hz)
        rw [h4, sum_smulRight_apply]
      rw [sum_smulRight_apply]
      simp only [h3]
      exact tendsto_finsetSum _ fun q _ => (hpt (q :: w) z hz).const_smul _
    rw [h1]
    exact tendsto_nhds_unique h2 (hpt (p :: w) z hz)
  have hfam : ∀ v, ContDiffOn ℝ ∞ (Gf v) (GLs n) :=
    GlobalTheory.T.closed_derivative_system_smooth n V (List (Bool × Fin n × Fin n)) Gf (fun p w => p :: w)
      (fun v z hz => (hhas v z hz).differentiableAt) (fun v p z hz => hRd v p z hz)
  refine ⟨Gf, hu, hfam [], ?_⟩
  intro w
  induction w with
  | nil => intro z _; rfl
  | cons p w ih =>
    intro z hz
    exact (Rd_congr ih (bs p) z hz).trans (hRd w p z hz)

end GlobalTheory.CompanionTheory.PresSobA.LimSmooth
