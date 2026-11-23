import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnfoldKernel

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.BoundedUnfold

theorem multiplicity_le (I : AutInst) (g : ℕ) (S : Set I.Ginf) (y z : I.GA) (hn : 1 ≤ I.n)
    (hS : ∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) :
    {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.Finite ∧
    (({γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.ncard : ℕ) : ℝ) ≤
      (1 + 4 * Real.sqrt I.n / tau1 I y ^ 2) ^ (2 * (I.n ^ 2 * I.f)) := by
  classical
  have hτ : 0 < tau1 I y := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y
  rcases Set.eq_empty_or_nonempty
      {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g} with h0 | ⟨γ0, hγ0⟩
  · rw [h0]
    refine ⟨Set.finite_empty, ?_⟩
    rw [Set.ncard_empty, Nat.cast_zero]
    positivity
  · obtain ⟨hCfin, hCcard⟩ :=
      GlobalTheory.RationalCount.count_le I y y (fun _ => Real.log 2) hn (fun _ => (Real.log_pos one_lt_two).le)

    have hf : ∀ γ ∈ {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g},
        (fun γ : GlobalTheory.RatDiscrete.ratSub I => γ.1 * γ0.1⁻¹) γ ∈
          {a : I.GA | a ∈ I.GFset ∧ (y⁻¹ * a * y).2 ∈ I.Kset ∧
            ∀ v, dOp (uMat ((y⁻¹ * a * y).1 v)) ≤ (fun _ => Real.log 2) v} := by
      intro γ hγ
      have hγ' : y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g := hγ
      have hγ0' : y⁻¹ * (γ0.1 * z) ∈ S ×ˢ I.Kg g := hγ0
      have key : y⁻¹ * (γ.1 * γ0.1⁻¹) * y = (y⁻¹ * (γ.1 * z)) * (y⁻¹ * (γ0.1 * z))⁻¹ := by
        group
      refine ⟨?_, ?_, ?_⟩
      · exact (GlobalTheory.RatDiscrete.ratSub I).mul_mem γ.2 ((GlobalTheory.RatDiscrete.ratSub I).inv_mem γ0.2)
      · rw [key]
        have h1 := hγ'.2.1
        have h2 := hγ0'.2.1
        simp only [AutInst.Kset, Set.mem_ofPred_eq] at h1 h2 ⊢
        rw [Prod.snd_mul, Prod.snd_inv]
        push_cast
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      · intro v
        rw [key, Prod.fst_mul, Prod.fst_inv]
        exact hS _ hγ'.1 _ hγ0'.1 v
    have hinj : Set.InjOn (fun γ : GlobalTheory.RatDiscrete.ratSub I => γ.1 * γ0.1⁻¹)
        {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g} :=
      fun a _ b _ hab => Subtype.ext (mul_right_cancel hab)
    have hAfin : {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.Finite :=
      Set.Finite.of_finite_image (hCfin.subset (Set.image_subset_iff.2 hf)) hinj
    refine ⟨hAfin, ?_⟩
    refine le_trans (Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn _ hf hinj hCfin)) (le_trans hCcard ?_)
    have hsum : (∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) = (I.f : ℝ) * Real.log 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, GlobalTheory.RationalCount.card_places]
    have hE : Real.exp ((∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) / I.f) ≤ 2 := by
      rw [hsum]
      rcases Nat.eq_zero_or_pos I.f with hf0 | hfpos
      · rw [hf0]; norm_num
      · have : (I.f : ℝ) ≠ 0 := by exact_mod_cast hfpos.ne'
        rw [mul_div_cancel_left₀ _ this, Real.exp_log two_pos]
    apply pow_le_pow_left₀ (by positivity)
    have h2 : 2 * Real.sqrt I.n * Real.exp ((∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) / I.f) /
        (tau1 I y * tau1 I y) ≤ 2 * Real.sqrt I.n * 2 / (tau1 I y * tau1 I y) := by
      gcongr
    calc _ ≤ 1 + 2 * Real.sqrt I.n * 2 / (tau1 I y * tau1 I y) := by linarith
      _ = 1 + 4 * Real.sqrt I.n / tau1 I y ^ 2 := by ring

theorem lintegral_le_multiplicity : ∀ (B : RowsAut) (S : Set B.I.Ginf) (y : B.I.GA) (Φ : B.I.GA → ENNReal), 1 ≤ B.I.n → 1 ≤ B.g → MeasurableSet S → (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) → Measurable Φ → (∀ γ ∈ B.I.GFset, ∀ z, Φ (γ * z) = Φ z) → (∀ k ∈ B.I.Kg B.g, ∀ z, Φ (z * (1, k)) = Φ z) → B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) ≤ ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * ∫⁻ z in B.fund, Φ z ∂(B.I.muA B.μf) := by
  intro B S y Φ hn hg hSm hS hΦ hΦl hΦr
  classical
  have hL : ∀ a : B.I.GA, Measurable (fun q : B.I.GA => a * q) := fun a =>
    (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf a).measurable
  have hKm : MeasurableSet (B.I.Kg B.g) :=
    ((GlobalTheory.CongTop.adelic_topology B.I).2.2.2.2.2.2 B.g hg).1.measurableSet
  have hUm : MeasurableSet (S ×ˢ B.I.Kg B.g) := hSm.prod hKm

  have step1 : B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) =
      ∫⁻ p in S ×ˢ B.I.Kg B.g, Φ (y * p) ∂(B.I.muA B.μf) := by
    rw [AutInst.muA, ← Measure.prod_restrict, lintegral_prod (fun p => Φ (y * p)) (hΦ.comp (hL y)).aemeasurable]
    have inner : ∀ a : B.I.Ginf, ∫⁻ k in B.I.Kg B.g, Φ (y * (a, k)) ∂B.μf =
        Φ (y * (a, 1)) * B.μf (B.I.Kg B.g) := by
      intro a
      rw [← setLIntegral_const]
      refine setLIntegral_congr_fun hKm (fun k hk => ?_)
      have e : y * (a, k) = y * (a, 1) * (1, k) := by
        rw [mul_assoc]
        congr 1
        exact Prod.ext (mul_one a).symm (one_mul k).symm
      rw [e, hΦr k hk]
    simp_rw [inner]
    rw [lintegral_mul_const (f := fun a : B.I.Ginf => Φ (y * (a, 1))) _
      (hΦ.comp ((hL y).comp measurable_prodMk_right))]
    exact mul_comm _ _

  have hH : Measurable (fun q : B.I.GA => (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q)) :=
    ((hΦ.comp (hL y)).indicator hUm).comp (hL y⁻¹)
  have step2 : ∫⁻ p in S ×ˢ B.I.Kg B.g, Φ (y * p) ∂(B.I.muA B.μf) =
      ∫⁻ q, (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q) ∂(B.I.muA B.μf) := by
    rw [← lintegral_indicator hUm,
      ← (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf y).lintegral_comp hH]
    congr 1
    funext p
    simp only [inv_mul_cancel_left]

  have hfd := GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec
  have : Countable (GlobalTheory.RatDiscrete.ratSub B.I) :=
    Set.Countable.to_subtype (s := (GlobalTheory.RatDiscrete.ratSub B.I : Set B.I.GA))
      (GlobalTheory.RatDiscrete.countable_GFset B.I)
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA := ⟨fun c => hL c.1⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun c s hs => (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf c.1).measure_preimage
      hs.nullMeasurableSet⟩

  have hpt : ∀ z : B.I.GA, ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
      (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) ≤
        ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * Φ z := by
    intro z
    obtain ⟨hAf, hAc⟩ := multiplicity_le B.I B.g S y z hn hS
    have hHA : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) =
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator
            (fun _ => Φ z) γ := by
      intro γ
      by_cases h : y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : GlobalTheory.RatDiscrete.ratSub B.I |
          y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g} from h)]
        show Φ (y * (y⁻¹ * (γ.1 * z))) = Φ z
        rw [mul_inv_cancel_left]
        exact hΦl γ.1 γ.2 z
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show γ ∉ {γ : GlobalTheory.RatDiscrete.ratSub B.I |
          y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g} from h)]
    have hsum1 : ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
        {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ =
        ∑ γ ∈ hAf.toFinset,
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ :=
      tsum_eq_sum (s := hAf.toFinset) (fun γ hγ => Set.indicator_of_notMem (by simpa using hγ) _)
    have hsum2 : ∑ γ ∈ hAf.toFinset,
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ =
        ∑ γ ∈ hAf.toFinset, Φ z :=
      Finset.sum_congr rfl (fun γ hγ => Set.indicator_of_mem (by simpa using hγ) _)
    rw [tsum_congr hHA, hsum1, hsum2, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hAf]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hAc
  calc B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I)
      = ∫⁻ q, (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q) ∂(B.I.muA B.μf) := by
        rw [step1, step2]
    _ = ∫⁻ z in B.fund, ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
          (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) ∂(B.I.muA B.μf) := by
        rw [hfd.lintegral_eq_tsum''
          (fun q : B.I.GA => (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q))]
        rw [lintegral_tsum (f := fun (γ : GlobalTheory.RatDiscrete.ratSub B.I) (z : B.I.GA) =>
            (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)))
          (fun γ => (hH.comp (hL γ.1)).aemeasurable)]
        simp only [Subgroup.smul_def]
        rfl
    _ ≤ ∫⁻ z in B.fund, ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^
          (2 * (B.I.n ^ 2 * B.I.f))) * Φ z ∂(B.I.muA B.μf) := lintegral_mono hpt
    _ = _ := lintegral_const_mul _ hΦ

end GlobalTheory.BoundedUnfold
