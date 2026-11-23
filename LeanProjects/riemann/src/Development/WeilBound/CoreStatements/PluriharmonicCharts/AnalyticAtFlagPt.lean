import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsHoloOnOfGerm
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValue
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicCompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFlagPointInOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ}

theorem analyticAt_flagPt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : FrameData ι Ψ N M.Ω M.blk)
    {b : E → (Σ k, baseIdx ι M.blk k) → ℂ} {h : Ψ → E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hb : ∀ q, AnalyticAt ℂ (fun u => b u q) w) (hv : ∀ q I, AnalyticAt ℂ (fun u => valAt M.x (F.u q I) (b u)) w)
    (hh : ∀ τ r s, AnalyticAt ℂ (fun u => h τ u r s) w) (q : Σ k, ι k) :
    AnalyticAt ℂ (fun u => FC.flagPt M F (b u) (fun τ => h τ u) q) w := by
  by_cases hk : ∀ p, M.blk p ≠ some q.1
  · simp only [FC.flagPt, dif_pos hk]
    exact hb _
  · simp only [FC.flagPt, dif_neg hk]
    exact Finset.analyticAt_fun_sum _ fun I _ => (hv q I).mul
      (Fib.analyticAt_minorIJ_of_entries _ w (hh _) _ _)

variable (BM : BaseMetric M n) {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {pr : X → BM.Rb.X}

theorem bvec_holo (hp : HoloMap A BM.Rb.A pr) {W : Set X} (hW : IsOpen W) {l : Fin BM.q}
    (hl : ∀ x ∈ W, pr x ∈ BM.O l) :
    (∀ q, A.HoloOn W fun x => FC.bvec BM l (pr x) q) ∧
      ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) →
        A.HoloOn W fun x => valAt M.x s (FC.bvec BM l (pr x)) := by
  have key := fun k => GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l e ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W)
    (pr ∘ (A.chart k).symm) ((A.chart k).isOpen_inter_preimage_symm hW)
    (hp.1.comp_continuousOn ((A.chart k).continuousOn_symm.mono Set.inter_subset_left))
    (fun m => (hp.2 k m).mono fun t ht => ⟨ht.1.1, ht.2⟩) (fun u hu => hl _ hu.2)
  exact ⟨fun q k => (key k).1 q, fun s hs k => (key k).2 s hs⟩

theorem step_of_orbit {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ} {z : (Σ k, ι k) → ℂ}
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (ho : SameOrbit z (FC.flagPt M F b h)) (p : Ψ × Fin N) (k : K)
    (hk : M.blk p = some k) : ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k,
      z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
  obtain ⟨c, hc, rfl⟩ := ho
  exact ⟨c k, hc k, fun m => by rw [← FC.flagPt_step M F b h hk m]⟩

theorem lowMat_props (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) ∧ IsLowerUni (lowMat c τ) :=
  ⟨fun a b h => (dif_neg fun e => h e.2).trans (if_neg fun e => h (by rw [e])),
    fun _ => (dif_neg fun e => lt_irrefl _ e.1).trans (if_pos rfl),
    fun _ _ h => (dif_neg fun e => lt_asymm h e.1).trans (if_neg h.ne)⟩

theorem lowMat_eq {c : LowIdx Ψ N j → ℂ} {τ : Ψ} {L : Matrix (Fin N) (Fin N) ℂ} (hb : IsBlockDiag j L)
    (hL : IsLowerUni L) (h : ∀ (a b : Fin N) (e : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)), c ⟨(τ, a, b), e⟩ = L a b) :
    lowMat c τ = L := by
  ext a b
  unfold lowMat
  split_ifs with h1 h2
  · exact h a b h1
  · rw [h2, hL.1]
  · rcases lt_or_gt_of_ne h2 with e | e
    · exact (hL.2 a b e).symm
    · exact (hb a b fun e' => h1 ⟨e, e'⟩).symm

theorem exists_holo_flags (hp : HoloMap A BM.Rb.A pr) {W : Set X} (hW : IsOpen W) {z : X → (Σ k, ι k) → ℂ}
    (hz : ∀ q, A.HoloOn W fun x => z x q) (hm : ∀ x ∈ W, z x ∈ mcPts (mCoordIdeal y))
    (hb : ∀ x ∈ W, SameOrbit (basePart M.blk (z x)) (BM.Rb.lift (pr x) (pr x))) {l : Fin BM.q}
    (hl : ∀ x ∈ W, pr x ∈ BM.O l) {x₀ : X} (hx₀ : x₀ ∈ W) :
    ∃ W' : Set X, IsOpen W' ∧ x₀ ∈ W' ∧ W' ⊆ W ∧ ∃ (h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ)
      (L : Ψ → X → Matrix (Fin N) (Fin N) ℂ), (∀ τ, IsBlockDiag j (h₀ τ) ∧ (h₀ τ).det ≠ 0) ∧
      (∀ τ a b, A.HoloOn W' fun x => L τ x a b) ∧ (∀ τ x, IsBlockDiag j (L τ x) ∧ IsLowerUni (L τ x)) ∧
      ∀ x ∈ W', SameOrbit (z x) (FC.flagPt M (BM.F l) (FC.bvec BM l (pr x)) fun τ => h₀ τ * L τ x) := by
  have hj := M.j_le
  have hF := BM.isFrame l
  have hg := GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l
  have hex := fun x (hx : x ∈ W) => GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l (pr x) (hl x hx) (z x) (hm x hx) (hb x hx)
  obtain ⟨h₀, hh₀, ho₀⟩ := hex x₀ hx₀
  let tw : Fin N → K → Ψ → Finset (Fin N) → X → ℂ := fun i k τ J x =>
    twMinor M (BM.F l) (FC.bvec BM l (pr x)) i k (h₀ τ)⁻¹ (z x) J
  have htw : ∀ i k τ J, A.HoloOn W (tw i k τ J) := by
    intro i k τ J m t ht
    have hv := fun I (q : Σ k, ι k) => (bvec_holo BM hp hW hl).2 ((BM.F l).u' I q)
      (fun b hb => ((hg b hb).2.1.2.1 q I).2) m t ht
    show AnalyticAt ℂ (fun w => tw i k τ J ((A.chart m).symm w)) t
    simp only [tw, twMinor, pluck]
    exact Finset.analyticAt_fun_sum _ fun I _ => analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun r _ => (hv I ⟨k, r⟩).mul (hz ⟨k, r⟩ m t ht))
  let T := {pk : (Ψ × Fin N) × K // M.blk pk.1 = some pk.2}
  let den : T → X → ℂ := fun t => tw t.1.1.2 t.1.2 t.1.1.1 (stepCols N j t.1.1.2)
  have tweq : ∀ x ∈ W, ∀ h' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h' τ)) →
      SameOrbit (z x) (FC.flagPt M (BM.F l) (FC.bvec BM l (pr x)) h') → ∀ t : T, ∃ α : ℂ, α ≠ 0 ∧
        den t x = α * minorIJ ((h₀ t.1.1.1)⁻¹ * h' t.1.1.1) (stepCols N j t.1.1.2) (stepCols N j t.1.1.2) := by
    intro x hx h' hb' ho t
    obtain ⟨α, hα, hzk⟩ := step_of_orbit ho t.1.1 t.1.2 t.2
    exact ⟨α, hα, GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M (BM.F l) _ t.1.1 t.1.2 _ _ _ α _ hF (hg _ (hl x hx)).1
      (hg _ (hl x hx)).2.1 t.2 (hb' _) hzk⟩
  refine ⟨{x | x ∈ W ∧ ∀ t, den t x ≠ 0}, isOpen_ne hW fun t => htw _ _ _ _, ⟨hx₀, fun t => ?_⟩, fun x hx => hx.1, h₀,
    fun τ x => lowMat (fun q : LowIdx Ψ N j =>
      lowRead M (BM.F l) (FC.bvec BM l (pr x)) h₀ (z x) q.1.1 q.1.2.1 q.1.2.2) τ, hh₀, fun τ a b => ?_,
    fun τ x => lowMat_props _ _, fun x hx => ?_⟩
  · obtain ⟨α, hα, e⟩ := tweq x₀ hx₀ h₀ (fun τ => (hh₀ τ).1) ho₀ t
    rw [e, Matrix.nonsing_inv_mul _ (hh₀ _).2.isUnit, CPts.minorIJ_one, mul_one]
    exact hα
  · by_cases h1 : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · simp only [lowMat, dif_pos h1, lowRead]
      rcases hk : M.blk (τ, stepOf N j b) with _ | k
      · exact fun _ => analyticOnNhd_const
      · intro m t ht
        exact AnalyticAt.div (htw (stepOf N j b) k τ _ m t ⟨ht.1, ht.2.1⟩) (htw (stepOf N j b) k τ _ m t ⟨ht.1, ht.2.1⟩)
          (ht.2.2 ⟨((τ, stepOf N j b), k), hk⟩)
    · simp only [lowMat, dif_neg h1]
      exact fun _ => analyticOnNhd_const
  · obtain ⟨h', hh', ho⟩ := hex x hx.1
    have hLU : ∀ τ, ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧
        U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ (h₀ τ)⁻¹ * h' τ = L * U := by
      intro τ
      refine GlobalTheory.T.block_LU_factorization N j _ hj (((hh₀ τ).1.inv (hh₀ τ).2.isUnit).mul (hh' τ).1) ?_ fun i hi => ?_
      · rw [Matrix.det_mul]
        exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hh₀ τ).2.isUnit).ne_zero (hh' τ).2
      · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 fun e => (M.blk_none (τ, i)).1 e hi
        obtain ⟨α, -, e⟩ := tweq x hx.1 h' (fun τ => (hh' τ).1) ho ⟨((τ, i), k), hk⟩
        have := hx.2 ⟨((τ, i), k), hk⟩
        rw [e] at this
        exact right_ne_zero_of_mul this
    choose L U hLb hLu hUb hUt hUd hLU using hLU
    have e1 : ∀ τ, lowMat (fun q : LowIdx Ψ N j =>
        lowRead M (BM.F l) (FC.bvec BM l (pr x)) h₀ (z x) q.1.1 q.1.2.1 q.1.2.2) τ = L τ := fun τ =>
      lowMat_eq (hLb τ) (hLu τ) fun a b e => LowRead.main K ι Φ y Ψ N j M (BM.F l) _ h₀ τ a b (z x) (h' τ) (L τ) (U τ)
        hF (hg _ (hl x hx.1)).1 (hg _ (hl x hx.1)).2.1 (hh' τ).1 (hLU τ) (hLb τ) (hLu τ) (hUb τ) (hUt τ)
        (fun c _ => hUd τ c) e.1 e.2 fun k hk => step_of_orbit ho (τ, stepOf N j b) k hk
    simp only [e1]
    have e2 : h' = fun τ => (h₀ τ * L τ) * U τ := funext fun τ => by
      rw [Matrix.mul_assoc, ← hLU, Matrix.mul_nonsing_inv_cancel_left _ _ (hh₀ τ).2.isUnit]
    refine orbit_trans ho ?_
    rw [e2]
    refine GlobalTheory.T.flag_point_triangular_change_orbit K ι Φ y Ψ N j M _ _ (fun τ => h₀ τ * L τ) U fun τ => ⟨hUb τ, hUt τ, ?_⟩
    rw [Matrix.det_of_upperTriangular (hUt τ)]
    exact Finset.prod_ne_zero_iff.2 fun c _ => hUd τ c

end PositivityTheory.Xgp.c_unif
