import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlatWeightExtends
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLineStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SamePotBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingWeightRegFamilyTransport
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviPullEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NotMemMcPtsTop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightDescendsOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsSmoothHermPullHerm
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MCoordIdealCompLeImageZ
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem central_regular {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {nb : ℕ} (m : Fin nb → ℕ) (W : Fin nb → Set X)
    (hL : IsPotential A L) (hs : IsSection A L s) (snc : IsSNC A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0)
    (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (th : LocPot X) (u : X → ℝ) (C₅ : ℝ)
    (hsw : IsSingWeight A L s th u C₅) (hneg : IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1))) :
    ∃ (u' : X → ℝ) (C₀ : ℝ), A.Smooth u' ∧ (∀ y ∉ bdry s, u' y = u y) ∧ IsPsh A (th + LocPot.ofFun u') ∧
      IsPsh A ((th + LocPot.ofFun u').rsmul (-1)) ∧ IsSingWeight A L s th u' C₀ ∧
      IsRegFamily A Θ L s th u' (fun _ => u') C₀ (Real.exp (-Real.exp 1)) ∧
      IsRegFamilyC2 A s u' fun _ => u' := by
  obtain ⟨hth, hsm, hpsh, hb⟩ := hsw
  have hlog : ∀ y, 1 ≤ Real.log (rW L s y) := fun y => by
    have h1 : Real.exp 1 ≤ rW L s y := by
      have := hn y
      unfold rW
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h1
  have hbd : ∀ y ∉ bdry s, |u y| ≤ |C₅| * Real.log (rW L s y) := fun y hy => by
    obtain ⟨h1, h2⟩ := hb y hy
    have h3 := hlog y
    have h4 : C₅ ≤ |C₅| := le_abs_self _
    have h5 : -|C₅| ≤ C₅ := neg_abs_le _
    have h6 : 0 ≤ |C₅| := abs_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  obtain ⟨u', hu', heq, hp1, hp2⟩ := GlobalTheory.CompanionTheory.Ar.PB.Flat.flat_weight_extends e X A L s nb m W hL hs snc hn th u |C₅| hth hsm hpsh hneg hbd
  obtain ⟨C₀, h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e X A Θ L s nb m W hL hs snc hn hΘ hΘp).2.2 th u' hth hu' hp1
  exact ⟨u', C₀, hu', heq, hp1, hp2, h1, h2, h3⟩

theorem deg0_orbit {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] (B : HermLine ρ) (hB : B.a = 0)
    {z z' : (Σ k, ρ k) → ℂ} (h : SameOrbit z z') : B.h z = B.h z' := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [B.smul c z' hc, hB]
  simp

theorem dy_eq_zero (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (k : K)
    (hk : k ∉ Set.range (Subtype.val : PartialFlagBlocks M p → K)) : M.dy p k = 0 := by
  have h1 : ¬ ∀ p', M.blk p' ≠ some k := fun h => hk ⟨⟨k, Or.inl h⟩, rfl⟩
  have h2 : M.blk p ≠ some k := fun h => hk ⟨⟨k, Or.inr h⟩, rfl⟩
  unfold FlagModel.dy
  rw [dif_neg h1, if_neg h2]

theorem step_member (hR : RegGlobalStatement) (hP : PullbackStatement) [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n e : ℕ} (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
    (hdim : e = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (pL : IsPotential R.A (BM.L.pullback pr hp.1))
    (sL : IsSection R.A (BM.L.pullback pr hp.1) fun x y => BM.s (pr x) (pr y))
    (nL : IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m fun k => pr ⁻¹' BM.W k)
    (p : Ψ × Fin N) :
    ∃ (ph : R.X → ℝ) (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine ι) (C₅ C t₀ : ℝ),
      IsStepMember BM R pr hp p ph phT line C₅ C t₀ := by
  have hv := isBlockMap_stepV M p
  obtain ⟨e', Rp, -, prp, hq, hpts, hch⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n e BM.Rb hdim (· = p) (PartialFlagBlocks M p)
    (stepIdx M p) Subtype.val (stepV M p) hv (mem_range_step M p)
  obtain ⟨pL', sL', nL', B, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection e' n Rp.X BM.Rb.X Rp.A BM.Rb.A BM.Bat prp hq BM.L BM.s BM.nb BM.m
    BM.W BM.potL BM.sec BM.snc BM.norm_le hch
  have hkeep : ∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) →
      k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) := fun k hk => ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨ph', C₅, hw1, -, hsw, hgb⟩ := GlobalTheory.T.partial_flag_bundle_metric_line K ι Φ y Ψ N j M n e BM p (PartialFlagBlocks M p) (stepIdx M p)
    Subtype.val (stepV M p) hv hkeep e' Rp prp hq B hpts pL' sL' nL' hB
  have hn' : ∀ x, logNormSec (BM.L.pullback prp hq.1) (fun x y => BM.s (prp x) (prp y)) x ≤ 0 :=
    fun x => BM.norm_le (prp x)
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA', hfs', hΘ'⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential (PartialFlagBlocks M p) (stepIdx M p) _ e' Rp
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ e R
  obtain ⟨h, hh, hso⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj (PartialFlagBlocks M p) (stepIdx M p) K ι Subtype.val (stepV M p) _ _ ⊤ e' e Rp R hv
    (GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal.mCoordIdeal_comp_le_imageZ K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) Φ y hv)
  obtain ⟨hfac, hinj⟩ := GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap.factor K ι Φ y Ψ N j M p n e e' BM.Rb R Rp pr prp h hb hpts hso
  have hreg : ∃ (ph₂ : Rp.X → ℝ) (phT₂ : ℝ → Rp.X → ℝ) (C₅₂ C t₀ : ℝ),
      IsSingWeight Rp.A (BM.L.pullback prp hq.1) (fun x y => BM.s (prp x) (prp y))
        (potOf Rp (fsHerm (stepIdx M p) fun k => M.dy p k.1)) ph₂ C₅₂ ∧
      IsRegFamily Rp.A (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) (BM.L.pullback prp hq.1)
        (fun x y => BM.s (prp x) (prp y)) (potOf Rp (fsHerm (stepIdx M p) fun k => M.dy p k.1)) ph₂ phT₂ C t₀ ∧
      IsRegFamilyC2 Rp.A (fun x y => BM.s (prp x) (prp y)) ph₂ phT₂ ∧
      (∀ x, prp x ∉ bdry BM.s → ph₂ x = ph' x) ∧
      ((p.2 : ℕ) + 1 = N → Rp.A.Smooth ph₂ ∧ (∀ t, phT₂ t = ph₂) ∧
        IsPsh Rp.A (potOf Rp (fsHerm (stepIdx M p) (fun k => M.dy p k.1)) + LocPot.ofFun ph₂) ∧
        IsPsh Rp.A ((potOf Rp (fsHerm (stepIdx M p) (fun k => M.dy p k.1)) + LocPot.ofFun ph₂).rsmul (-1))) := by
    by_cases hc : (p.2 : ℕ) + 1 = N
    · have flat := GlobalTheory.CompanionTheory.Ar.PB.FA.Flat.flat_off_boundary K ι Φ y Ψ N j M n BM p hc (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) hv
        (fun k hk => hkeep k (Or.inl hk)) e' Rp prp hq ph' hpts hw1
      obtain ⟨u', C₀, hu', heq, p1, p2, s1, r1, c1⟩ := central_regular Rp.A
        (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _ _ BM.m _ pL' sL' nL' hn' (hA' _ hfs') hΘ' _ ph' C₅ hsw flat.2
      exact ⟨u', fun _ => u', C₀, C₀, _, s1, r1, c1, heq, fun _ => ⟨hu', fun _ => rfl, p1, p2⟩⟩
    · obtain ⟨C, t₀, phT, r, c⟩ := hR Rp.A B (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _ _ BM.m _ (hA' _ hfs') hΘ'
        pL' sL' nL' hn' hB _ ph' C₅ hsw hgb
      exact ⟨ph', phT, C₅, C, t₀, hsw, r, c, fun _ _ => rfl, fun h => absurd h hc⟩
  obtain ⟨ph₂, phT₂, C₅₂, C, t₀, s2, r2, c2, heq, hcen⟩ := hreg
  have hw := GlobalTheory.CompanionTheory.Ar.PB.FA.weight_descends_of_sameOrbit K ι Φ y Ψ N j M p e e' R Rp h (BM.hom p) (fsHerm ι (M.dy p)) ph'
    {x | prp x ∉ bdry BM.s} (BM.hom_deg p) hso hw1
  obtain rfl : pr = prp ∘ h := funext fun x => (hfac x).symm
  obtain ⟨C', t₀', h1, h2, h3⟩ := hP Rp.A R.A h hh (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _
    (potOf R (fsHerm ι fun _ => 1)) _ BM.m _ BM.m _ (hA' _ hfs') hΘ' (hA _ hfs) hΘ pL' sL' nL' hn' nL _ ph₂ phT₂ C₅₂ C t₀
    s2 r2 c2
  have hfsd : IsPotential R.A (potOf R (fsHerm ι (M.dy p))) := hA _ (GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
  have hsp := GlobalTheory.CompanionTheory.Ar.PB.FA.BlockPot.samePot_block K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) _ _ _ _ e e' R Rp h hh (M.dy p) hv
    (dy_eq_zero M p) hso
  have tr := GlobalTheory.CompanionTheory.Ar.PB.Transport.singWeight_regFamily_transport e R.X R.A (potOf R (fsHerm ι fun _ => 1)) _ _ _ _ (ph₂ ∘ h) (fun t => phT₂ t ∘ h) C₅₂ C'
    t₀' (hA _ hfs) sL hfsd h1.1 hsp
  obtain ⟨T, hT⟩ : ∃ T, T = min (min t₀ t₀') (Real.exp (-1)) := ⟨_, rfl⟩
  have hT0 : 0 < T := by
    rw [hT]
    exact lt_min (lt_min r2.1 h2.1) (Real.exp_pos _)
  have hT1 : T ≤ t₀ := by rw [hT]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hT2 : T ≤ t₀' := by rw [hT]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hT3 : T ≤ Real.exp (-1) := by rw [hT]; exact min_le_right _ _
  have reg' := (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e R.X R.A _ _ _ BM.nb BM.m _ pL sL nL hn (hA _ hfs) hΘ).2.1 _ _ _ _ _ |C'| T le_rfl hT0 hT2
    hT3 (tr.2 h2) hfsd
  have hB2 : ∀ t, ∃ Bt : HermLine (stepIdx M p), Bt.a = 0 ∧ (0 < t → t ≤ T → IsSmoothHerm Bt ∧
      ∀ x, Real.log (Bt.h (Rp.lift x x)) = phT₂ t x) := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ T
    · obtain ⟨Bt, a0, hs, hl⟩ := GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth _ _ _ e' Rp (phT₂ t) (r2.2.2 t ht.1 (ht.2.trans hT1)).1
      exact ⟨Bt, a0, fun _ _ => ⟨hs, hl⟩⟩
    · exact ⟨fsHerm _ 0, rfl, fun h1 h2 => absurd ⟨h1, h2⟩ ht⟩
  choose Bf hBa hBs using hB2
  choose line hla hlon hls hll using fun t => GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine.exists_stepLine K ι Φ y Ψ N j M p (Bf t) (hBa t)
  refine ⟨ph₂ ∘ h, fun t => phT₂ t ∘ h, line, C₅₂, |C'|, T, tr.1 h1, reg', h3, hla, hlon, ?_, ?_, ?_, ?_⟩
  · intro t h0 ht
    obtain ⟨hs, hl⟩ := hBs t h0 ht
    refine ⟨hls t hs, fun x => ?_⟩
    rw [hll t _ (R.mem x x (R.mem_U x)).1, ← deg0_orbit (Bf t) (hBa t) (hso x), hl]
    rfl
  · intro x hx
    rw [hw x hx]
    simp only [Function.comp]
    rw [heq _ hx]
  · intro x x' hx hk
    have e1 := hinj x x' hx hk
    exact ⟨by simp only [Function.comp, e1], fun t => by simp only [Function.comp, e1]⟩
  · intro hc t
    obtain ⟨hsm, hc1, p1, p2⟩ := hcen hc
    have hpp := GlobalTheory.CompanionTheory.Ar.PB.PshPull.isPsh_pull e e' R.X Rp.X R.A Rp.A h hh _ _ ph₂ hfsd (hA' _ (GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)) hsm hsp
    refine ⟨?_, ?_, ?_⟩
    · show IsPsh R.A ((_ + LocPot.ofFun (phT₂ t ∘ h)).rsmul (-1))
      rw [hc1 t]
      exact hpp.2 p2
    · show IsPsh R.A (_ + LocPot.ofFun (phT₂ t ∘ h))
      rw [hc1 t]
      exact hpp.1 p1
    · show phT₂ t ∘ h = _
      rw [hc1 t]

open scoped ContDiff

theorem degree_id_self {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) : IsDegreeOff A A id 1 ∅ := by
  have hA : A.IsAnalyticSubset ∅ := fun x =>
    ⟨Set.univ, isOpen_univ, trivial, 1, fun _ _ => 1, fun _ _ _ _ => analyticAt_const, by ext; simp⟩
  refine ⟨hA, interior_empty, hA, interior_empty, fun x _ => by simp, fun j k y hy _ hk => ?_⟩
  set E := (A.chart j).symm.trans (A.chart k) with he
  have hs : y ∈ E.source := ⟨hy, hk⟩
  have hf : DifferentiableAt ℂ (A.chart k ∘ (A.chart j).symm) y := (A.holo j k y ⟨hy, hk⟩).differentiableAt
  have ht := E.map_source hs
  have hg : DifferentiableAt ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y) :=
    (A.holo k j _ ⟨ht.1, ht.2⟩).differentiableAt
  have hc := fderiv_comp y hg hf
  have hid : (A.chart j ∘ (A.chart k).symm) ∘ (A.chart k ∘ (A.chart j).symm) =ᶠ[𝓝 y] id := by
    filter_upwards [E.open_source.mem_nhds hs] with w hw
    exact E.left_inv hw
  rw [hid.fderiv_eq, fderiv_id] at hc
  intro h0
  have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => LinearMap.det (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) hc
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id] at this
  erw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp] at this
  have h0' : LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := h0
  rw [h0', mul_zero] at this
  exact one_ne_zero this

theorem common_bound {σ : Type} [Finite σ] (f : σ → ℝ) : ∃ M : ℝ, ∀ a, f a ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨M, fun a => hM ⟨a, rfl⟩⟩

theorem common_scale {σ : Type} [Finite σ] (f : σ → ℝ) (hf : ∀ a, 0 < f a) : ∃ t : ℝ, 0 < t ∧ ∀ a, t ≤ f a := by
  obtain ⟨M, hM⟩ := common_bound fun a => (f a)⁻¹
  by_cases he : Nonempty σ
  · obtain ⟨a₀⟩ := he
    have hM0 : 0 < M := lt_of_lt_of_le (inv_pos.2 (hf a₀)) (hM a₀)
    refine ⟨M⁻¹, inv_pos.2 hM0, fun a => ?_⟩
    exact inv_le_of_inv_le₀ (hf a) (hM a)
  · exact ⟨1, one_pos, fun a => absurd ⟨a⟩ he⟩

theorem IsStepMember.mono {M : FlagModel y Ψ N j} {n e : ℕ} {BM : BaseMetric M n}
    {R : AnLogRes (mCoordIdeal y) ⊤ e} {pr : R.X → BM.Rb.X} {hp : HoloMap R.A BM.Rb.A pr} {p : Ψ × Fin N}
    {ph : R.X → ℝ} {phT : ℝ → R.X → ℝ} {line : ℝ → HermLine ι} {C₅ C t₀ D₅ D T : ℝ}
    (m₁ : ∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph C₅ →
      IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph C₅')
    (m₂ : ∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) →
      IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph phT C t₀ →
      IsPotential R.A th →
      IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph phT C' t₀')
    (h : IsStepMember BM R pr hp p ph phT line C₅ C t₀) (h₅ : C₅ ≤ D₅) (hD : |C| ≤ D) (hT0 : 0 < T) (hT : T ≤ t₀)
    (hT1 : T ≤ Real.exp (-1)) : IsStepMember BM R pr hp p ph phT line D₅ D T := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨m₁ _ _ _ _ h₅ a1, m₂ _ _ _ _ _ _ _ hD hT0 hT hT1 a2 a1.1, a3, a4, a5, fun t h0 h1 => a6 t h0 (h1.trans hT), a7⟩

theorem flagAn_of_res (hR : RegGlobalStatement) (hP : PullbackStatement) [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n : ℕ} (d : ℕ) (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ (d + 1))
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (harith : IsArithVar (mCoordIdeal y) (d + 2))
    (hdim : d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (hch : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin (d + 1) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 1)),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i))) :
    Nonempty (FlagAn BM d) := by
  obtain ⟨pL, sL, nL, B, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection (d + 1) n R.X BM.Rb.X R.A BM.Rb.A BM.Bat pr hp BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ (d + 1) R
  have hfsa : ∀ a : K → ℤ, IsSmoothHerm (fsHerm ι a) := GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm
  choose ph phT line C₅ C t₀ hm using fun p => step_member hR hP M BM R pr hp hdim hb pL sL nL p
  obtain ⟨m₁, m₂, m₃⟩ := GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members (d + 1) R.X R.A (potOf R (fsHerm ι fun _ => 1)) _ _ BM.nb BM.m _ pL sL nL hn
    (hA _ hfs) hΘ
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ ∞ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  have hpsh0 : IsPsh R.A (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)) := by
    intro x jj z hz w
    have e1 : (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)).φ x ∘ (R.A.chart jj).symm =
        (potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart jj).symm := by
      funext u
      show (potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ) = _
      rw [add_zero]
      rfl
    rw [e1]
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hΘ x jj z ⟨hz.1, hz.2.1⟩ w hw).le
  obtain ⟨C₀, s0, r0, c0⟩ := m₃ _ 0 (hA _ hfs) hsm0 hpsh0
  obtain ⟨D₅, hD₅⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim C₀ C₅
  obtain ⟨D, hD⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim |C₀| fun p => |C p|
  obtain ⟨T, hT0, hT⟩ := common_scale (fun o : Option (Option (Ψ × Fin N)) =>
    o.elim (Real.exp (-1)) fun o' => o'.elim (Real.exp (-Real.exp 1)) t₀) (by
      rintro (_ | _ | p)
      · exact Real.exp_pos _
      · exact Real.exp_pos _
      · exact (hm p).2.1.1)
  have hT1 : T ≤ Real.exp (-1) := hT none
  have hm' : ∀ p, IsStepMember BM R pr hp p (ph p) (phT p) (line p) D₅ D T := fun p =>
    IsStepMember.mono m₁ m₂ (hm p) (hD₅ (some p)) (hD (some p)) hT0 (hT (some (some p))) hT1
  have s0' := m₁ _ _ _ _ (hD₅ none) s0
  have r0' := m₂ _ _ _ _ _ _ _ (hD none) hT0 (hT (some none)) hT1 r0 (hA _ hfs)
  let S : AnSys (d + 1) (Option (Ψ × Fin N)) :=
    { X := R.X
      A := R.A
      Θ := potOf R (fsHerm ι fun _ => 1)
      L := BM.L.pullback pr hp.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := hn
      th := fun o => o.elim (potOf R (fsHerm ι fun _ => 1)) fun p => potOf R (fsHerm ι (M.dy p))
      ph := fun o => o.elim 0 ph
      phT := fun o => o.elim (fun _ => 0) phT
      C₅ := D₅
      C := D
      t₀ := T
      sing := by
        rintro (_ | p)
        · exact s0'
        · exact (hm' p).1
      reg := by
        rintro (_ | p)
        · exact r0'
        · exact (hm' p).2.1
      c2 := by
        rintro (_ | p)
        · exact c0
        · exact (hm' p).2.2.1 }
  let Re : Realis S (mCoordIdeal y) :=
    { arith := harith
      J := ⊤
      R := R
      π := id
      holo := ⟨continuous_id, fun jj k => R.A.holo jj k⟩
      deg := 1
      deg_pos := one_pos
      br := ∅
      degree := degree_id_self R.A
      ref := fun o => o.elim (fsHerm ι fun _ => 1) fun p => fsHerm ι (M.dy p)
      ref_smooth := by
        rintro (_ | p)
        · exact hfs
        · exact hfsa _
      ref_pot := by
        rintro (_ | p) <;>
        exact fun x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
          fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
      line := fun o t => o.elim (fsHerm ι fun _ => 1) fun p => line p t
      line_deg := by
        rintro (_ | p) t
        · rfl
        · exact (hm' p).2.2.2.1 t
      line_smooth := by
        rintro (_ | p) t h0 h1
        · exact hfs
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).1
      line_eq := by
        rintro (_ | p) t h0 h1 x
        · show _ = _ + (0 : ℝ)
          rw [add_zero]
          rfl
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).2 x }
  refine ⟨{ S := S, Re := Re, J_top := rfl, deg_one := rfl, br_empty := rfl, ref_some := fun _ => rfl, ref_none := rfl,
            line_none := fun _ => rfl, ph_none := ⟨rfl, fun _ => rfl⟩, pos_none := ?_, pr := pr, pr_holo := hp,
            pr_eq := hb, L_eq := rfl, s_eq := rfl, hom_eq := ?_, step := ?_, step_ph := ?_, flat := ?_ }⟩
  · refine ⟨1, one_pos, fun t x jj z _ w => ?_⟩
    have e1 : (S.potT none t + S.Θ.rsmul (-1)).φ x ∘ (S.A.chart jj).symm = fun _ => (0 : ℝ) := by
      funext u
      show ((potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ)) + (-1) * (potOf R (fsHerm ι fun _ => 1)).φ x _ = 0
      ring
    rw [e1]
    simp [levi]
  · exact fun p x hx => (hm' p).2.2.2.2.2.2.1 x hx
  · exact fun p t => (hm' p).2.2.2.2.1 t
  · exact fun p x x' h1 h2 => (hm' p).2.2.2.2.2.2.2.1 x x' h1 h2
  · exact fun p h1 t => (hm' p).2.2.2.2.2.2.2.2 h1 t

theorem flagAn_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (FlagAn BM d) := by
  intro hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM harith hd
  obtain ⟨e, R, he, pr, hp, hpts, hch⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n (d + 1) BM.Rb hd (fun _ => True) K ι id id
    isBlockMap_id (fun k => ⟨fun _ => by
      by_cases h : ∀ p', M.blk p' ≠ some k
      · exact Or.inl h
      · push_neg at h
        obtain ⟨p, hp⟩ := h
        exact Or.inr ⟨p, trivial, hp⟩, fun _ => ⟨k, rfl⟩⟩)
  obtain rfl := he fun _ => trivial
  refine flagAn_of_res hI.regGlobal hI.pullback M d BM R pr hp harith hd (fun x => ?_) hch
  obtain ⟨z, -, hz, ho⟩ := hpts x
  have hz' : z = R.lift x x := hz
  rw [← hz']
  exact ho

end GlobalTheory.CompanionTheory.Ar.PB.FA
