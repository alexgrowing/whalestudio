import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem lift_analyticAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {n e : ℕ}
    (R : AnLogRes P J n) {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → R.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ bp) (V ∩ bp ⁻¹' (R.A.chart k).source)) {u₀ : Fin e → ℂ} (hu : u₀ ∈ V)
    (p : Σ k, ι k) : AnalyticAt ℂ (fun u => R.lift (bp u₀) (bp u) p) u₀ := by
  obtain ⟨k, hk⟩ := R.A.cover (bp u₀)
  have h1 : AnalyticAt ℂ (R.A.chart k ∘ bp) u₀ := ha k u₀ ⟨hu, hk⟩
  have h2 : AnalyticAt ℂ ((fun y => R.lift (bp u₀) y p) ∘ (R.A.chart k).symm) ((R.A.chart k ∘ bp) u₀) :=
    R.holo (bp u₀) p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k (bp u₀)) ∈ R.U (bp u₀)
      rw [(R.A.chart k).left_inv hk]
      exact R.mem_U _⟩
  refine (h2.comp h1).congr ?_
  have hW : V ∩ bp ⁻¹' (R.A.chart k).source ∈ 𝓝 u₀ :=
    (hc.isOpen_inter_preimage hV (R.A.chart k).open_source).mem_nhds ⟨hu, hk⟩
  filter_upwards [hW] with u hu'
  simp only [Function.comp, (R.A.chart k).left_inv hu'.2]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem bvec_analyticAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source))
    (hO : ∀ u ∈ V, bp u ∈ BM.O l) {u₀ : Fin e → ℂ} (hu : u₀ ∈ V) (q : Σ k, baseIdx ι M.blk k) :
    AnalyticAt ℂ (fun u => FC.bvec BM l (bp u) q) u₀ := by
  have hne : BM.Rb.lift (bp u₀) (bp u₀) ⟨q.1, (BM.F l).c q.1⟩ ≠ 0 :=
    FibreCount.chart_ne ((BM.good l _ (hO u₀ hu)).1 q.1)
  have hq := (lift_analyticAt BM.Rb hV hc ha hu q).div
    (lift_analyticAt BM.Rb hV hc ha hu ⟨q.1, (BM.F l).c q.1⟩) hne
  refine hq.congr ?_
  have hW : V ∩ bp ⁻¹' (BM.Rb.U (bp u₀)) ∈ 𝓝 u₀ :=
    (hc.isOpen_inter_preimage hV (BM.Rb.isOpen_U _)).mem_nhds ⟨hu, BM.Rb.mem_U _⟩
  filter_upwards [hW] with u hu'
  obtain ⟨c, hc0, ec⟩ := BM.Rb.compat (bp u₀) (bp u) (bp u) ⟨hu'.2, BM.Rb.mem_U _⟩
  show BM.Rb.lift (bp u₀) (bp u) q / BM.Rb.lift (bp u₀) (bp u) ⟨q.1, (BM.F l).c q.1⟩ =
    BM.Rb.lift (bp u) (bp u) q / BM.Rb.lift (bp u) (bp u) ⟨q.1, (BM.F l).c q.1⟩
  rw [ec]
  exact mul_div_mul_left _ _ (hc0 q.1)

theorem valAt_analyticAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hO : ∀ u ∈ V, bp u ∈ BM.O l)
    {u₀ : Fin e → ℂ} (hu : u₀ ∈ V) (hw : ∀ q, AnalyticAt ℂ (fun u => FC.bvec BM l (bp u) q) u₀) {s : M.Ω}
    (hs : RegAt M.x (mCoordIdeal (FC.bvec BM l (bp u₀))) s) :
    AnalyticAt ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) u₀ := by
  obtain ⟨d, g, h, hg, hh, hQ, eq⟩ := hs
  have hE : ∀ (z : (Σ k, baseIdx ι M.blk k) → ℂ) (f : MRing (baseIdx ι M.blk)),
      eval z (map (Int.castRingHom ℂ) f) = aeval z f := fun z f => by
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
  have aG : AnalyticAt ℂ (fun u => aeval (FC.bvec BM l (bp u)) g) u₀ := AnalyticAt.aeval_mvPolynomial hw g
  have aH : AnalyticAt ℂ (fun u => aeval (FC.bvec BM l (bp u)) h) u₀ := AnalyticAt.aeval_mvPolynomial hw h
  have h0 : aeval (FC.bvec BM l (bp u₀)) h ≠ 0 := fun e0 => hQ (mem_mCoordIdeal_of_aeval_eq_zero _ hh e0)
  refine (aG.div aH h0).congr ?_
  filter_upwards [hV.mem_nhds hu, aH.continuousAt.eventually_ne h0] with u hu' hne
  have hz := (bvec_good K ι Φ y Ψ N j M n BM l _ (hO u hu')).1
  have h1 : eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) h) ≠ 0 := by rwa [hE]
  have h2 : aeval M.x h ≠ 0 := fun e0 => h1 (hz.2 h (mem_mCoordIdeal_of_aeval_eq_zero M.x hh e0))
  have hv : IsValueAt M.x s (FC.bvec BM l (bp u))
      (eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) g) / eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) h)) :=
    ⟨d, g, h, hg, hh, h2, eq, h1, rfl⟩
  rw [valAt_eq hz hv, hE, hE]
  rfl

theorem bvec_val_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q) (e : ℕ) (V : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → BM.Rb.X), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V) ∧ ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) → AnalyticOnNhd ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) V := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l e V bp hV hc ha hO
  have hb : ∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V := fun q u hu =>
    bvec_analyticAt BM l hV hc ha hO hu q
  exact ⟨hb, fun s hs u hu => valAt_analyticAt BM l hV hO hu (fun q => hb q u hu) (hs _ (hO u hu))⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
