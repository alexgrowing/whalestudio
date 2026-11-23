import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopologyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistanceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SetLIntegralLeMulOfEncardLe

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff ENNReal

namespace GlobalTheory.LocMass

theorem setLIntegral_le_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ)
    {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) (hinv : ∀ᵐ y ∂μ, ∀ γ : Γ, f ((γ : G) * y) = f y)
    {S : Set G} (hS : MeasurableSet S) (N : ℝ≥0∞) (hN' : N ≠ ⊤)
    (hN : ∀ z : G, (({γ : Γ | (γ : G) * z ∈ S}.encard : ℕ∞) : ℝ≥0∞) ≤ N) :
    ∫⁻ y in S, f y ∂μ ≤ N * ∫⁻ y in D, f y ∂μ := by
  first
  | (rename_i h_1 h_2 h_3 h_4 h_5 h_7 h_9; revert G h_1 h_2 h_3 h_4 h_5 μ h_7 Γ h_9 D hD f hf hinv S hS N hN' hN; exact @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le)
  | exact @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le
  | exact _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le
  | (apply _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le ..)

theorem encard_le {G : Type} [Group G] (Γ : Subgroup G) (U T : Set G) (x z : G)
    (hT : ∀ γ ∈ Γ, ∀ u ∈ U, ∀ u' ∈ U, x⁻¹ * γ * x = u * u'⁻¹ → γ ∈ T) :
    {γ : Γ | (γ : G) * z ∈ (fun g => x⁻¹ * g) ⁻¹' U}.encard ≤ T.encard := by
  rcases Set.eq_empty_or_nonempty {γ : Γ | (γ : G) * z ∈ (fun g => x⁻¹ * g) ⁻¹' U} with h | ⟨γ₀, h0⟩
  · rw [h]; simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : Γ => ((γ * γ₀⁻¹ : Γ) : G)) ?_ ?_
    · intro γ hγ
      refine hT _ (γ * γ₀⁻¹).2 _ hγ _ h0 ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro a _ b _ hab
      exact mul_right_cancel (Subtype.ext hab)

theorem local_mass_le : ∀ (B : RowsAut) (U : Set B.I.GA), 1 ≤ B.I.n → IsCompact U → (∀ u ∈ U, u.2 ∈ B.I.Kset) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : B.I.L2 B.μf B.fund) (x : B.I.GA), ∫⁻ g in U, (‖B.I.ext y (x * g)‖₊ : ENNReal) ^ 2 ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (C * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) * ‖y‖ ^ 2) := by
  intro B U hn hU hK
  obtain ⟨hT2, hL, hS, -, -, ⟨K, hKK⟩, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology B.I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain B.I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have hfund := B.fund_spec
  have hD := hfd B.μf B.fund hfund
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have hr : ∀ y, ∃ γ : Γ, B.I.rep B.fund y = (γ : B.I.GA) * y ∧ B.I.rep B.fund y ∈ B.fund := by
    intro y
    have h := hfund.2.1 y
    have e : B.I.rep B.fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set B.I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  have hb : ∀ v : InfinitePlace B.I.F, ∃ r : ℝ, 0 ≤ r ∧ ∀ u ∈ U, ∀ u' ∈ U,
      dOp (uMat ((u * u'⁻¹).1 v)) ≤ r := by
    intro v
    have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((p.1 * p.2⁻¹).1 v)) :=
      (GlobalTheory.Count.Cartan.cartan_distances B.I.n (B.I.ε v)).2.2.2.2.comp
        ((continuous_apply v).comp (continuous_fst.comp (continuous_fst.mul continuous_snd.inv)))
    obtain ⟨r, hr⟩ := (hU.prod hU).bddAbove_image hc.continuousOn
    exact ⟨max r 0, le_max_right _ _, fun u hu u' hu' =>
      (hr ⟨(u, u'), ⟨hu, hu'⟩, rfl⟩).trans (le_max_left _ _)⟩
  choose r hr0 hrb using hb
  refine ⟨(3 * Real.sqrt B.I.n) ^ (2 * B.I.n ^ 2 * B.I.f) * Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v),
    by positivity, fun y x => ?_⟩
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.count_rational_elements_bounded_distance B.I x x r hn hr0
  obtain ⟨hinv, hmeas⟩ := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.2.2 y
  set N : ℝ := (3 * Real.sqrt B.I.n) ^ (2 * B.I.n ^ 2 * B.I.f) *
    Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) with hN
  have hNe : (3 * Real.sqrt B.I.n / (tau1 B.I x * tau1 B.I x)) ^ (2 * B.I.n ^ 2 * B.I.f) *
      Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) = N := by
    rw [hN, div_eq_mul_inv, mul_inv, mul_pow, mul_pow (tau1 B.I x)⁻¹, ← pow_add,
      show 2 * B.I.n ^ 2 * B.I.f + 2 * B.I.n ^ 2 * B.I.f = 4 * B.I.n ^ 2 * B.I.f by ring]
    ring
  rw [hNe] at hcard
  have hN0 : 0 ≤ N := (Nat.cast_nonneg _).trans hcard
  have hUm : MeasurableSet U := hU.measurableSet
  have hSm : MeasurableSet ((fun g => x⁻¹ * g) ⁻¹' U) := measurable_const_mul _ hUm
  have h1 := (measurePreserving_mul_left (B.I.muA B.μf) x⁻¹).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft x⁻¹) (fun g => (‖B.I.ext y (x * g)‖₊ : ℝ≥0∞) ^ 2) U
  simp only [mul_inv_cancel_left] at h1
  rw [← h1]
  have h2 := setLIntegral_le_mul hD (f := fun g => (‖B.I.ext y g‖₊ : ℝ≥0∞) ^ 2)
    (hmeas.enorm.pow_const 2)
    (hinv.mono fun z hz γ => by rw [hz γ (hΓ ▸ γ.2)]) hSm (ENNReal.ofReal N) ENNReal.ofReal_ne_top
    (fun z => by
      have := encard_le Γ U {γ ∈ B.I.GFset | (x⁻¹ * γ * x).2 ∈ B.I.Kset ∧
          ∀ v, dOp (uMat ((x⁻¹ * γ * x).1 v)) ≤ r v} x z (fun γ hγ u hu u' hu' e => by
        refine ⟨hΓ ▸ hγ, ?_, fun v => ?_⟩
        · rw [e, ← hKK]
          have h1 : u.2 ∈ K := by rw [← SetLike.mem_coe, hKK]; exact hK u hu
          have h2 : u'.2 ∈ K := by rw [← SetLike.mem_coe, hKK]; exact hK u' hu'
          exact K.mul_mem h1 (K.inv_mem h2)
        · rw [e]; exact hrb v u hu u' hu')
      refine (ENat.toENNReal_le.2 this).trans ?_
      rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hcard)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hN0]
  congr 1
  have h3 : ∫⁻ g in B.fund, (‖B.I.ext y g‖₊ : ℝ≥0∞) ^ 2 ∂(B.I.muA B.μf) =
      ∫⁻ g in B.fund, ‖(y : B.I.GA → ℂ) g‖ₑ ^ (2 : ℝ) ∂(B.I.muA B.μf) := by
    refine lintegral_congr_ae ((GlobalTheory.RightRegFund.ae_rep_eq_self hD hfund.1 hr).mono fun z hz => ?_)
    simp only [AutInst.ext, hz]
    rw [ENNReal.rpow_two]; rfl
  rw [h3, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, Lp.enorm_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

end GlobalTheory.LocMass
