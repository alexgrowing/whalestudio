import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtHolomorphicComposition
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_finTail {d : ℕ} (u : Fin (d + 1) → ℂ) :
    AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) u := by
  have h : (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) =
      ⇑(ContinuousLinearMap.pi fun i : Fin d =>
        (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) := by
    funext u i
    rfl
  rw [h]
  exact ContinuousLinearMap.analyticAt _ _

theorem analyticAt_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : Type} [Fintype n]
    [DecidableEq n] (A : E → Matrix n n ℂ) (x : E) (h : ∀ r s, AnalyticAt ℂ (fun u => A u r s) x) :
    AnalyticAt ℂ (fun u => (A u).det) x := by
  simp only [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_minorIJ_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    (A : E → Matrix (Fin N) (Fin N) ℂ) (x : E) (h : ∀ r s, AnalyticAt ℂ (fun u => A u r s) x)
    (I J : Finset (Fin N)) : AnalyticAt ℂ (fun u => minorIJ (A u) I J) x := by
  by_cases e : I.card = J.card
  · simp only [minorIJ, dif_pos e]
    exact analyticAt_det_of_entries _ x fun r s => h _ _
  · simp only [minorIJ, dif_neg e]
    exact analyticAt_const

theorem analyticAt_flagAt_entry {Ψ : Type} [DecidableEq Ψ] {N d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (u₀ : Fin (d + 1) → ℂ)
    (hH : ∀ τ'' r s, AnalyticAt ℂ (fun w => H τ'' w r s) (Fin.tail u₀)) (r s : Fin N) :
    AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => flagAt H τ ca cb (u 0) (Fin.tail u) τ' r s) u₀ := by
  have hHt : ∀ τ'' r s, AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => H τ'' (Fin.tail u) r s) u₀ :=
    fun τ'' r s => (hH τ'' r s).comp (analyticAt_finTail u₀)
  have h0 : AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => u 0) u₀ :=
    (ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℂ) →L[ℂ] ℂ).analyticAt _
  unfold flagAt
  by_cases h : τ' = τ
  · simp only [if_pos h, Matrix.mul_apply, Matrix.add_apply]
    refine Finset.analyticAt_fun_sum _ fun t _ => (hHt _ _ _).mul (analyticAt_const.add ?_)
    by_cases e : cb = t ∧ ca = s
    · simpa only [Matrix.single_apply, if_pos e] using h0
    · simpa only [Matrix.single_apply, if_neg e] using analyticAt_const
  · simp only [if_neg h]
    exact hHt _ _ _

theorem sameOrbit_basePart {K : Type} {ι : K → Type} {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem coord_ne_zero_of_X_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 := fun h0 => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem exists_normalised_exact {M : FlagModel y Ψ N j} (F : FrameData ι Ψ N M.Ω M.blk) (z₀ : (Σ k, ι k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (hne : ∀ k : NonPluckerBlocks M.blk, z₀ ⟨k.1, F.c k⟩ ≠ 0)
    (hex : ∀ τ' i, M.ExactAt F (τ', i) z₀ (h τ')) :
    ∃ z : (Σ k, ι k) → ℂ, SameOrbit z₀ z ∧ (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) ∧
      ∀ τ' i, M.ExactAt F (τ', i) z (h τ') := by
  by_cases hp : Nonempty (Ψ × Fin N)
  · obtain ⟨⟨τ₀, i₀⟩⟩ := hp
    exact ⟨z₀, ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩, (hex τ₀ i₀).1, hex⟩
  · have hb : ∀ (k : K) p, M.blk p ≠ some k := fun k p => (hp ⟨p⟩).elim
    refine ⟨fun q => z₀ q / z₀ ⟨q.1, F.c ⟨q.1, hb q.1⟩⟩,
      ⟨fun k => z₀ ⟨k, F.c ⟨k, hb k⟩⟩, fun k => hne ⟨k, hb k⟩, ?_⟩, ?_, fun τ' i => (hp ⟨(τ', i)⟩).elim⟩
    · funext q
      rw [mul_div_cancel₀ _ (hne ⟨q.1, hb q.1⟩)]
    · rintro ⟨k, hk⟩
      exact div_self (hne ⟨k, hb k⟩)

theorem exact_points_holomorphic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a ca cb : Fin N) (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∃ zex : (Fin (d + 1) → ℂ) → (Σ k, ι k) → ℂ, (∀ q', AnalyticOnNhd ℂ (fun u => zex u q') {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un}) ∧ ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → zex u ∈ mcPts (mCoordIdeal y) ∧ ∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) (zex u) ∧ SameOrbit (basePart M.blk (zex u)) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧ ∀ τ' i, M.ExactAt (BM.F l) (τ', i) (zex u) (flagAt H τ ca cb (u 0) (Fin.tail u) τ') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a ca cb X q Un Gn ΦYn ΦWn l H bp hUn hD
  obtain ⟨hH, hbc, hba, hbp, -, hex, -⟩ := hD
  have hbij := realis_bijective_of_degree_one K ι (d + 1) _ FA.S _ FA.Re FA.deg_one FA.br_empty
  have hyh : IsMultiHomogIdeal (mCoordIdeal y) :=
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y
  have key : ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → ∃ z : (Σ k, ι k) → ℂ,
      z ∈ mcPts (mCoordIdeal y) ∧ (∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) z) ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧
      (∀ τ' i, M.ExactAt (BM.F l) (τ', i) z (flagAt H τ ca cb (u 0) (Fin.tail u) τ')) ∧
      ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1 := by
    intro u hu
    obtain ⟨x₀, hx₀⟩ := hbij.2 (ΦYn u)
    obtain ⟨z₀, ho, hb, he⟩ := hex u hu x₀ hx₀
    have hgood := BM.good l _ (hbp _ hu).1.1
    have hne : ∀ k : NonPluckerBlocks M.blk, z₀ ⟨k.1, (BM.F l).c k⟩ ≠ 0 := by
      intro k
      obtain ⟨c, hc, hcz⟩ := hb
      have h1 := congrFun hcz ⟨k, (BM.F l).c k⟩
      have h2 : basePart M.blk z₀ ⟨k, (BM.F l).c k⟩ = z₀ ⟨k.1, (BM.F l).c k⟩ := rfl
      rw [← h2, h1]
      exact mul_ne_zero (hc k) (coord_ne_zero_of_X_notMem (hgood.1 k))
    obtain ⟨z, hz, hn, hz'⟩ := exists_normalised_exact (BM.F l) z₀ _ hne he
    refine ⟨z, ?_, ?_, ?_, hz', hn⟩
    · exact mem_mcPts_of_sameOrbit hyh (orbit_symm (orbit_trans ho hz))
        (FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀))
    · intro x₁ hx₁
      obtain rfl := hbij.1 (hx₁.trans hx₀.symm)
      exact orbit_trans ho hz
    · exact orbit_trans (orbit_symm (sameOrbit_basePart M.blk hz)) hb
  choose! zex hz using key
  refine ⟨zex, ?_, fun u hu => ⟨(hz u hu).1, fun x₀ hx =>
    ⟨(hz u hu).2.1 x₀ hx, (hz u hu).2.2.1, (hz u hu).2.2.2.1⟩⟩⟩
  rintro ⟨k, m⟩ u₀ hu₀
  have hu₀' : (Fin.tail u₀ : Fin d → ℂ) ∈ Un := hu₀
  have htail : Tendsto (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) (𝓝 u₀) (𝓝 (Fin.tail u₀)) :=
    (analyticAt_finTail u₀).continuousAt
  have hevU : ∀ᶠ u : Fin (d + 1) → ℂ in 𝓝 u₀, (Fin.tail u : Fin d → ℂ) ∈ Un := htail (hUn.mem_nhds hu₀')
  have hgood₀ := BM.good l _ (hbp _ hu₀').1.1
  by_cases hk : ∃ p, M.blk p = some k
  · obtain ⟨p, hp⟩ := hk
    have hval : ∀ s, RegAt M.x (mCoordIdeal (BM.Rb.lift (bp (Fin.tail u₀)) (bp (Fin.tail u₀)))) s →
        AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => valAt M.x s (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u)))) u₀ :=
      fun s hs => (analyticAt_valAt_lift_family (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x s d n BM.Rb Un bp (Fin.tail u₀)
        hUn hu₀' hbc hba hs).comp (analyticAt_finTail u₀)
    have hsum : AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => ∑ I,
        valAt M.x ((BM.F l).u ⟨k, m⟩ I) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) *
          minorIJ (flagAt H τ ca cb (u 0) (Fin.tail u) p.1) I (stepCols N j p.2)) u₀ :=
      Finset.analyticAt_fun_sum _ fun I _ => (hval _ ((hgood₀.2.1 _ I).1)).mul
        (analyticAt_minorIJ_of_entries _ _ (analyticAt_flagAt_entry H τ ca cb p.1 u₀
          (fun τ'' r s => hH τ'' r s _ hu₀')) _ _)
    refine hsum.congr ?_
    filter_upwards [hevU] with u hu
    obtain ⟨-, -, hb, he, -⟩ := hz u hu
    rw [(he p.1 p.2).2 k hp m]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [valAt_eq_of_sameOrbit (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _))
      (orbit_symm hb)]
  · have hkb : ∀ p, M.blk p ≠ some k := fun p hp => hk ⟨p, hp⟩
    set kb : NonPluckerBlocks M.blk := ⟨k, hkb⟩ with hkb'
    set b₀ := bp (Fin.tail u₀) with hb₀
    have hlift : ∀ q : Σ k, baseIdx ι M.blk k,
        AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => BM.Rb.lift b₀ (bp (Fin.tail u)) q) u₀ :=
      fun q => (analyticAt_comp_of_holo_in_charts d n BM.Rb.X BM.Rb.A Un bp (Fin.tail u₀) (BM.Rb.U b₀)
        (fun x => BM.Rb.lift b₀ x q) hUn hu₀' hbc hba (BM.Rb.isOpen_U _) (BM.Rb.mem_U _)
        (BM.Rb.holo b₀ q)).comp (analyticAt_finTail u₀)
    have hden : BM.Rb.lift b₀ (bp (Fin.tail u₀)) ⟨kb, (BM.F l).c kb⟩ ≠ 0 :=
      coord_ne_zero_of_X_notMem (hgood₀.1 kb)
    refine ((hlift ⟨kb, m⟩).div (hlift ⟨kb, (BM.F l).c kb⟩) hden).congr ?_
    have hca : ContinuousAt bp (Fin.tail u₀) := hbc.continuousAt (hUn.mem_nhds hu₀')
    filter_upwards [hevU, htail (hca ((BM.Rb.isOpen_U b₀).mem_nhds (BM.Rb.mem_U b₀)))] with u hu hbu
    obtain ⟨-, -, hb, -, hn⟩ := hz u hu
    obtain ⟨c, hc, hcz⟩ := orbit_trans hb (BM.Rb.compat (bp (Fin.tail u)) b₀ (bp (Fin.tail u)) ⟨BM.Rb.mem_U _, hbu⟩)
    have h1 : c kb * BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ = 1 := by
      rw [← hn kb, hcz]
    have h2 : zex u ⟨k, m⟩ = c kb * BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩ := congrFun hcz ⟨kb, m⟩
    have h3 : BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ ≠ 0 := right_ne_zero_of_mul_eq_one h1
    show BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩ / BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ = zex u ⟨k, m⟩
    rw [h2, div_eq_iff h3]
    linear_combination (-(BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩)) * h1

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
