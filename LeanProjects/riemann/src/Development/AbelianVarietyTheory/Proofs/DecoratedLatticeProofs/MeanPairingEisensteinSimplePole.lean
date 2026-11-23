import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Filter Topology Set Metric

namespace GlobalTheory.RegSch.EisensteinPairing

variable {D : D7} {T T₀ : HSp D} {r : ℕ} {d : HypDec T T₀ r} {b : GL (Fin T.rank) (AE D)} {s₀ : ℂ} {j k : ℕ}

theorem eisenstein_analytic_half_plane (hA : EisensteinContinues d b) (h : GA D T) :
    AnalyticOnNhd ℂ (sphericalEisenstein d b h) (rightOf (rhoH T r)) := by
  have e : sphericalEisenstein d b h = fun s => ∑' q, (fun _ => (1 : ℂ)) q *
      npow ((fun q => GlobalTheory.Eis.term (stab d) (GQ T) (iwAbs (absDet d) (Kmax T b)) h q) q) (s - (-(rhoH T r : ℂ))) := by
    funext s
    simp only [sphericalEisenstein, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add]
  rw [e]
  refine GlobalTheory.Eis.analyticOnNhd_tsum_npow (fun _ => iwAbs_pos _ _ _) fun s hs => ?_
  have := hA.1 s hs h
  simpa only [GlobalTheory.Eis.CosetConv, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add] using this

theorem eisenstein_left_invariant_rational (hI : HasIw d (Kmax T b)) {γ : GA D T} (hγ : γ ∈ GQ T) (h : GA D T) :
    sphericalEisenstein d b (γ * h) = sphericalEisenstein d b h := by
  funext s
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (stab d ⊓ GQ T) (sphericalSection d b s) := by
    intro δ hδ g
    obtain ⟨u, hu⟩ := GlobalTheory.EisCont.det_onX_rat d ⟨δ, hδ.1⟩ hδ.2
    have h1 : absDet d ⟨δ, hδ.1⟩ = 1 := by
      rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
      exact absE_inclR u
    have h2 := hI.isIwasawa.iwAbs_left ⟨δ, hδ.1⟩ g
    rw [h1, one_mul] at h2
    exact congrArg (npow · _) h2
  exact GlobalTheory.Eis.leftInv_cosetSum hL γ hγ h

theorem regularAt_succ (h : EisensteinRegularAt d b s₀ k) : EisensteinRegularAt d b s₀ (k + 1) := by
  obtain ⟨ε, H, hr, e, hd, hc, C, N, hb⟩ := h
  refine ⟨ε, fun s g => (s - s₀) * H s g, hr, fun s hs h0 g => by simp only [e s hs h0]; ring,
    fun g => (differentiableOn_id.sub_const _).mul (hd g), (by fun_prop : ContinuousOn (fun x : ℂ × _ => x.1 - s₀) _).mul hc,
    ε * C, N, fun s hs g => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (mem_ball_iff_norm.1 hs).le (hb s hs g) (norm_nonneg _) hr.le

theorem regularAt_pred (h : EisensteinRegularAt d b s₀ (k + 1)) (hp : ∀ g, PoleLE (sphericalEisenstein d b g) s₀ j) (hj : j ≤ k) :
    EisensteinRegularAt d b s₀ k := by
  obtain ⟨ε, H, hr, e, hd, hc, C, N, hb⟩ := h
  have h0 : ∀ g, H s₀ g = 0 := fun g => by
    obtain ⟨E, hE, -⟩ := id (hp g)
    obtain ⟨c, hc⟩ := hE.poleLE_iff.1 (hp g)
    have h1 : Tendsto (fun s => (s - s₀) ^ (k + 1 - j)) (𝓝[≠] s₀) (𝓝 0) :=
      (Continuous.tendsto' (by fun_prop) s₀ 0 (by simp; omega)).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s₀}ᶜ))) ((zero_mul c ▸ h1.mul hc).congr' ?_)
    filter_upwards [hE.cont_eventuallyEq, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)]
      with s h2 h3 h4
    rw [e s h4 h3, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega), ← h2]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.Eis.dslope_family hr hd hc hb h0
  refine ⟨ε / 2, fun s g => dslope (H · g) s₀ s, half_pos hr, fun s hs hs' g => ?_, h1, h2, C / ε, N, fun s hs g => ?_⟩
  · have := sub_ne_zero.2 hs'
    simp only [dslope_of_ne _ hs', slope_def_field, h0, e s (ball_subset_ball (by linarith) hs) hs']
    field_simp
    ring
  · rw [div_mul_eq_mul_div]; exact h3 s hs g

theorem regularAt_of_poleLE (h : EisensteinRegularAt d b s₀ k) (hp : ∀ g, PoleLE (sphericalEisenstein d b g) s₀ j) :
    EisensteinRegularAt d b s₀ j := by
  rcases le_total k j with hk | hk
  · exact Nat.le_induction h (fun _ _ => regularAt_succ) j hk
  · exact Nat.decreasingInduction (motive := fun i _ => j ≤ i → EisensteinRegularAt d b s₀ i)
      (fun i _ ih hi => regularAt_pred (ih (by omega)) hp hi) (fun _ => h) hk le_rfl

theorem meanPair_const_mul (m : Measure (GA D T)) (F E : GA D T → ℂ) (c : ℂ) :
    meanPair T m F (fun h => c * E h) = c * meanPair T m F E := by
  simp only [meanPair, MeasureTheory.average]
  rw [← MeasureTheory.integral_const_mul]
  refine congrArg _ (funext fun q => ?_)
  simp only [GlobalTheory.AutomorphicL2Unitary.descend, mul_left_comm]

theorem pair_family {m : Measure (GA D T)} (hm : m.IsHaarMeasure) {F : GA D T → ℂ} (hF : GlobalTheory.Grow.RapidDec T F)
    {A : ℂ → GA D T → ℂ} {ε : ℝ} (hinv : ∀ s ∈ ball s₀ ε, ∀ γ ∈ GQ T, ∀ h, A s (γ * h) = A s h)
    (hd : ∀ h, DifferentiableOn ℂ (A · h) (ball s₀ ε))
    (hc : ContinuousOn (fun x : ℂ × GA D T => A x.1 x.2) (ball s₀ ε ×ˢ univ)) {C : ℝ} {N : ℕ}
    (hb : ∀ s ∈ ball s₀ ε, ∀ h, ‖A s h‖ ≤ C * GlobalTheory.Grow.height T h ^ N) :
    (∀ s ∈ ball s₀ ε, Integrable (descend (GQ T) fun h => F h * A s h) (autMeasure T m)) ∧
      DifferentiableOn ℂ (fun s => meanPair T m F (A s)) (ball s₀ ε) := by
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have hbi := (GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D T m hm F hF N).const_mul (C * 2 ^ N)
  have hmeas : ∀ s ∈ ball s₀ ε, AEStronglyMeasurable (descend (GQ T) fun h => F h * A s h) (autMeasure T m) := by
    intro s hs
    have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ T) fun h => F h * A s h := fun γ hγ g => by
      simp only [hF.left hγ, hinv s hs γ hγ]
    have hcont : Continuous (A s) := hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    refine Measurable.aestronglyMeasurable (measurable_from_quotient.2 ?_)
    have h' : (descend (GQ T) (fun h => F h * A s h) ∘ Quotient.mk'') = fun h => F h * A s h :=
      funext fun g => hL.descend_mk g
    rw [h']
    exact (hF.continuous.mul hcont).measurable
  have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := autMeasure T m) (F := fun q s => descend (GQ T) (fun h => F h * A s h) q)
    (isOpen_ball (x := s₀) (ε := ε)) hmeas (ae_of_all _ fun q => (hd _).const_mul _)
    fun x hx => ⟨ball s₀ ε, isOpen_ball.mem_nhds hx, _, hbi, ae_of_all _ fun q y hy => by
      have h1 := GlobalTheory.Grow.norm_le_quotHeight_pow (hinv y hy) (hb y hy) q.out
      show ‖F q.out * A y q.out‖ ≤ _
      rw [norm_mul, mul_comm, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)⟩
  refine ⟨fun s hs => (this.2 s hs).1, ?_⟩
  simp only [meanPair, MeasureTheory.average_eq]
  exact this.1.const_smul _

theorem pair_regular (hI : HasIw d (Kmax T b)) {m : Measure (GA D T)} (hm : m.IsHaarMeasure) {F : GA D T → ℂ}
    (hF : GlobalTheory.Grow.RapidDec T F) (hk : EisensteinRegularAt d b s₀ k) :
    ∃ (M : ℂ → ℂ) (E : GA D T → ℂ), AnalyticAt ℂ M s₀ ∧ M s₀ = meanPair T m F E ∧
      Integrable (descend (GQ T) fun h => F h * E h) (autMeasure T m) ∧
      (∀ h, Tendsto (fun s => (s - s₀) ^ k * cont (sphericalEisenstein d b h) s) (𝓝[≠] s₀) (𝓝 (E h))) ∧
      M =ᶠ[𝓝[≠] s₀] fun s => (s - s₀) ^ k * meanPair T m F fun h => cont (sphericalEisenstein d b h) s := by
  obtain ⟨ε, H, hr, e, hd, hc, C, N, hb⟩ := hk
  have ht : ∀ h, Tendsto (fun s => (s - s₀) ^ k * cont (sphericalEisenstein d b h) s) (𝓝[≠] s₀) (𝓝 (H s₀ h)) := fun h => by
    refine (((hd h).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)] with w h1 h2
    exact e w h2 h1 h
  have hinv : ∀ s ∈ ball s₀ ε, ∀ γ ∈ GQ T, ∀ h, H s (γ * h) = H s h := by
    intro s hs γ hγ g
    rcases eq_or_ne s s₀ with rfl | h0
    · have h1 := ht (γ * g)
      rw [eisenstein_left_invariant_rational hI hγ] at h1
      exact tendsto_nhds_unique h1 (ht g)
    · rw [e s hs h0, e s hs h0, eisenstein_left_invariant_rational hI hγ]
  obtain ⟨hi, hdiff⟩ := pair_family hm hF hinv hd hc hb
  refine ⟨_, H s₀, hdiff.analyticAt (ball_mem_nhds _ hr), rfl, hi s₀ (mem_ball_self hr), ht, ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)] with w h1 h2
  rw [← meanPair_const_mul]
  exact congrArg _ (funext (e w h2 h1))

end GlobalTheory.RegSch.EisensteinPairing

open GlobalTheory.RegSch.EisensteinPairing in

theorem GlobalTheory.RegSch.mean_pairing_eisenstein_continues : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → EisensteinContinues d b → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ F : GA D T → ℂ, GlobalTheory.Grow.RapidDec T F → Continues (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) ∧ PoleLE (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) (rhoH T r) 1 ∧ ResidueAt (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) (rhoH T r) (eisensteinResidue d b * meanPair T m F 1) ∧ ∀ (s : ℂ) (E : GA D T → ℂ), (∀ h, HolValueAt (sphericalEisenstein d b h) s (E h)) → Integrable (descend (GQ T) fun h => F h * E h) (autMeasure T m) ∧ HolValueAt (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) s (meanPair T m F E) := by
  intro D T T₀ r d b _ hI hA m hm F hF
  set Z : ℂ → ℂ := fun s => meanPair T m F fun h => cont (sphericalEisenstein d b h) s with hZ
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, hk⟩ := hA.2.2.1 s₁
    obtain ⟨M, E, han, -, -, -, e⟩ := pair_regular hI hm hF hk
    have h1 : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * M s) s₁ := (h1.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, e] with w h1 h2
    rw [h2, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
  have hext : IsMerExt (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) univ Z :=
    ⟨isRightDomain_univ, fun s _ => hmer s, rhoH T r, fun s hs =>
      congrArg (meanPair T m F) (funext fun h => eqOn_cont (eisenstein_analytic_half_plane hA h) hs)⟩
  have key : ∀ (s₁ : ℂ) (j : ℕ) (E : GA D T → ℂ), (∀ h, PoleLE (sphericalEisenstein d b h) s₁ j) →
      (∀ h, CoeffAt (sphericalEisenstein d b h) s₁ (-j) (E h)) →
      Integrable (descend (GQ T) fun h => F h * E h) (autMeasure T m) ∧
        Tendsto (fun s => (s - s₁) ^ j * Z s) (𝓝[≠] s₁) (𝓝 (meanPair T m F E)) := by
    intro s₁ j E hp hc
    obtain ⟨k, hk⟩ := hA.2.2.1 s₁
    obtain ⟨M, E', han, h0, hi, ht, e⟩ := pair_regular hI hm hF (regularAt_of_poleLE hk hp)
    have hE : E' = E := funext fun h => by
      obtain ⟨H, hH, -⟩ := id (hp h)
      refine tendsto_nhds_unique (ht h) ((hH.tendsto_of_poleLE (hp h) (hc h)).congr' ?_)
      filter_upwards [hH.cont_eventuallyEq] with w hw
      rw [hw]
    subst hE
    exact ⟨hi, (h0 ▸ han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' e⟩
  have hρ := (key (rhoH T r) 1 (fun h => eisensteinResidue d b * (1 : GA D T → ℂ) h) (fun h => (hA.2.2.2.2 h).1)
    fun h => by simpa using (hA.2.2.2.2 h).2).2
  rw [meanPair_const_mul] at hρ
  refine ⟨⟨Z, hext⟩, (hext.isExtAt trivial).poleLE_iff.2 ⟨_, hρ⟩, (hext.isExtAt trivial).coeffAt_of_tendsto hρ,
    fun s E hE => ?_⟩
  obtain ⟨h1, h2⟩ := key s 0 E (fun h => (holValueAt_iff_poleLE.1 (hE h)).1) fun h => by simpa using (hE h).valueAt
  exact ⟨h1, (hext.isExtAt trivial).holValueAt_iff.2 (by simpa using h2)⟩
