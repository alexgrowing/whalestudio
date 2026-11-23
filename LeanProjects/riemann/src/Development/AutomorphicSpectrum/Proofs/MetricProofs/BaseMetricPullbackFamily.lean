import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsNullOfLocallyInZeros
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicCompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
import ReciprocityTheory.AnalyticForms.PotentialTheory.HomogeneousLiftHolomorphicOnSnd
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem section_eq_zero_iff {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {b y : X} (hy : y ∈ L.U b) : s b y = 0 ↔ s y y = 0 := by
  have h := hs.2 b y y ⟨hy, L.mem_U y⟩
  have e1 := Real.exp_ne_zero (-L.φ b y)
  have e2 := Real.exp_ne_zero (-L.φ y y)
  constructor
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right e2)
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right e1)

theorem isNull_off_bigCell : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (e : ℕ) (X' : Type) [TopologicalSpace X'] (A' : FinHolAtlas e X') (U' : X' → Set X') (lf : X' → X' → (Σ k, ι k) → ℂ) (pr' : X' → BM.Rb.X) (l : Fin BM.q), HoloMap A' BM.Rb.A pr' → (∀ x, IsOpen (U' x)) → (∀ x, x ∈ U' x) → (∀ x p, A'.HoloOn (U' x) (fun y => lf x y p)) → (∀ x, ∀ y ∈ U' x, SameOrbit (lf x y) (lf y y)) → (∀ x, pr' x ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, pr' x' ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x')) (lf x' x') p ≠ 0) → IsNull A' {x | pr' x ∈ BM.O l ∧ (pr' x ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x)) (lf x x) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM e X' _ A' U' lf pr' l hpr hUo hUm hlf hor hden
  have hsec := BM.sec

  let f : X' → X' → ℂ := fun x w => BM.s (pr' x) (pr' w) *
    ∏ p : Ψ × Fin N, FC.plk M (BM.F l) (FC.bvec BM l (pr' w)) (lf x w) p
  let Wd : X' → Set X' := fun x => U' x ∩ pr' ⁻¹' (BM.O l ∩ BM.L.U (pr' x))
  have hWo : ∀ x, IsOpen (Wd x) := fun x =>
    (hUo x).inter (((BM.O_open l).inter (BM.L.isOpen_U _)).preimage hpr.1)

  have hne : ∀ x, ∀ w ∈ Wd x, pr' w ∉ bdry BM.s →
      (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' w)) (lf w w) p ≠ 0) → f x w ≠ 0 := by
    intro x w hw hb hp
    refine mul_ne_zero (fun h0 => hb ((section_eq_zero_iff hsec hw.2.2).1 h0)) ?_
    refine Finset.prod_ne_zero_iff.2 fun p _ => ?_
    exact (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p (hor x w hw.1)).2 (hp p)

  have hholo : ∀ x, A'.HoloOn (Wd x) (f x) := by
    intro x
    have h1 : A'.HoloOn (Wd x) fun w => BM.s (pr' x) (pr' w) :=
      fun c => (GlobalTheory.CompanionTheory.Ar.PB.SncPull.holoOn_comp_pr hpr (hsec.1 (pr' x)) c).mono
        fun t ht => ⟨ht.1, ht.2.2.2⟩
    have h2 : ∀ p : Ψ × Fin N, A'.HoloOn (Wd x) fun w =>
        FC.plk M (BM.F l) (FC.bvec BM l (pr' w)) (lf x w) p := by
      intro p c
      have hV : IsOpen ((A'.chart c).target ∩ (A'.chart c).symm ⁻¹' Wd x) :=
        (A'.chart c).isOpen_inter_preimage_symm (hWo x)
      have hval := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l e _ (pr' ∘ (A'.chart c).symm) hV
        (hpr.1.comp_continuousOn ((A'.chart c).continuousOn_symm.mono fun t ht => ht.1))
        (fun k => (hpr.2 c k).mono fun t ht => ⟨ht.1.1, ht.2⟩)
        (fun t ht => ht.2.2.1)
      have hreg : ∀ (q : Σ k, ι k) (I : Finset (Fin N)), ∀ b ∈ BM.O l,
          RegAt M.x (mCoordIdeal (FC.bvec BM l b)) ((BM.F l).u' I q) := fun q I b hb =>
        (((GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l b hb).2.1).2.1 q I).2
      unfold FC.plk
      rcases hb : M.blk p with _ | k
      · simpa [Function.comp_def] using analyticOnNhd_const
      · simp only [Option.elim]
        have : ∀ m : ι k, AnalyticOnNhd ℂ (fun t => valAt M.x ((BM.F l).u' (stepCols N j p.2) ⟨k, m⟩)
            (FC.bvec BM l ((pr' ∘ (A'.chart c).symm) t)) * lf x ((A'.chart c).symm t) ⟨k, m⟩)
            ((A'.chart c).target ∩ (A'.chart c).symm ⁻¹' Wd x) := fun m =>
          (hval.2 _ (hreg _ _)).mul (((hlf x ⟨k, m⟩) c).mono fun t ht => ⟨ht.1, ht.2.1⟩)
        intro t ht
        have := Finset.analyticAt_fun_sum Finset.univ fun m _ => this m t ht
        exact this
    refine FinHolAtlas.HoloOn.mul' h1 ?_
    intro c t ht
    exact Finset.analyticAt_fun_prod Finset.univ fun p _ => h2 p c t ht
  refine GlobalTheory.CompanionTheory.Ar.PB.NullLocal.isNull_of_locally_in_zeros e X' A' _ fun x hx => ⟨Wd x, f x, hWo x, ⟨hUm x, hx.1, BM.L.mem_U _⟩, hholo x, ?_, ?_⟩
  · rintro w ⟨hw, hwO, hwZ⟩
    rcases hwZ with hb | ⟨p, hp⟩
    · exact mul_eq_zero_of_left ((section_eq_zero_iff hsec hw.2.2).2 hb) _
    · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ p) ?_)
      by_contra h0
      exact (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p (hor x w hw.1)).1 h0 hp
  · rintro V hV ⟨x₁, hx₁⟩ hVW
    obtain ⟨x', hx'V, hx'b, hx'p⟩ := hden x₁ (hVW hx₁).2.1 V hV hx₁
    exact ⟨x', hx'V, hne x x' (hVW hx'V) hx'b.2 hx'p⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
