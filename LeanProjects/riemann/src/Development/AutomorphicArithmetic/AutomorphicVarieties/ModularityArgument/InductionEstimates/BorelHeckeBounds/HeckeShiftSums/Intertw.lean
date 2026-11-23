import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SwapInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LongCell
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecStr
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepsIntegralMemClosedSubmodule

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Cell

variable {K : Type} [Field K] [NumberField K]

private theorem nn_add (X Y : UPos (2 + 2) 2 → 𝔸[K]) : nn X * nn Y = nn (X + Y) := by
  first
    | exact (unipOne_add 2 X Y).symm
    | exact unipOne_add 2 X Y

private theorem nn_continuous : Continuous (nn (K := K)) := continuous_unipOne 2

private theorem hh_lv (a b : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)) : HH (lv a b t * g) = t + HH g := by
  have := (hpSpec (K := K)).1 0 a b t g
  rwa [show nn (K := K) 0 = 1 from unipOne_zero 2, one_mul] at this

private theorem hh_nn (X : UPos (2 + 2) 2 → 𝔸[K]) (g : G1 K (2 + 2)) : HH (nn X * g) = HH g := by
  have := (hpSpec (K := K)).1 X 1 1 0 g
  rwa [(blkLaws (K := K)).2.2.1, mul_one, zero_add] at this

private theorem form (Y : UPos (2 + 2) 2 → 𝔸[K]) (a b : G1 K 2) (t : ℝ) (k : G1 K (2 + 2)) :
    ∃ e : (UPos (2 + 2) 2 → 𝔸[K]) ≃ₜ+ (UPos (2 + 2) 2 → 𝔸[K]),
      (unipMeasure K (2 + 2) 2).map e = ENNReal.ofReal (Real.exp (4 * t)) • unipMeasure K (2 + 2) 2 ∧
      ∀ X, w0 K * nn X * (nn Y * lv a b t * k) = lv b a (-t) * (w0 K * nn (e (X + Y)) * k) := by
  obtain ⟨e, he, hm⟩ := adMeas a b t
  refine ⟨e, hm, fun X => ?_⟩
  have hw := (blkLaws (K := K)).2.2.2.2.2.2.2.2.2.1 a b t
  calc w0 K * nn X * (nn Y * lv a b t * k) = w0 K * (nn X * nn Y * lv a b t) * k := by group
    _ = w0 K * (lv a b t * nn (e (X + Y))) * k := by rw [nn_add, he]
    _ = (w0 K * lv a b t) * nn (e (X + Y)) * k := by group
    _ = lv b a (-t) * (w0 K * nn (e (X + Y)) * k) := by rw [hw]; group

private theorem supp (x : G1 K (2 + 2)) (R : ℝ) :
    ∃ C : Set (UPos (2 + 2) 2 → 𝔸[K]), IsCompact C ∧ ∀ X, -R ≤ HH (w0 K * nn X * x) → X ∈ C := by
  obtain ⟨Y, a, b, t, k, hk, rfl⟩ := iwa x
  obtain ⟨e, -, he⟩ := form Y a b t k
  obtain ⟨C, hC, hs⟩ := (longCell (K := K)).2 (R - t)
  refine ⟨(fun Z => e.symm Z - Y) '' C, hC.image (by fun_prop), fun X hX => ?_⟩
  rw [he, hh_lv] at hX
  exact ⟨e (X + Y), hs _ k hk (by linarith), by simp⟩

private theorem bd (G : G1 K (2 + 2) → ℂ) (B R : ℝ) (hB : ∀ g, ‖G g‖ ≤ B) (hR : ∀ g, G g ≠ 0 → |HH g| ≤ R) (s : ℝ) :
    ∃ M : ℝ, ∀ x : G1 K (2 + 2), HH x = s → ‖∫ X, G (w0 K * nn X * x) ∂unipMeasure K (2 + 2) 2‖ ≤ M := by
  obtain ⟨C, hC, hs⟩ := (longCell (K := K)).2 (R - s)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  refine ⟨B * (ENNReal.ofReal (Real.exp (4 * s)) * unipMeasure K (2 + 2) 2 C).toReal, fun x hx => ?_⟩
  obtain ⟨Y, a, b, t, k, hk, rfl⟩ := iwa x
  have ht : t = s := by
    have := (hpSpec (K := K)).1 Y a b t k
    rw [hx, ((hpSpec (K := K)).2.1 k hk).1, add_zero] at this
    exact this.symm
  subst ht
  obtain ⟨e, hm, he⟩ := form Y a b t k
  set A : Set (UPos (2 + 2) 2 → 𝔸[K]) := (fun X => e (X + Y)) ⁻¹' C with hA
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hAm : unipMeasure K (2 + 2) 2 A = ENNReal.ofReal (Real.exp (4 * t)) * unipMeasure K (2 + 2) 2 C := by
    have h1 : A = (fun X => X + Y) ⁻¹' (e ⁻¹' C) := rfl
    have hem : Measurable (e : (UPos (2 + 2) 2 → 𝔸[K]) → (UPos (2 + 2) 2 → 𝔸[K])) := (map_continuous e).measurable
    rw [h1, measure_preimage_add_right, ← Measure.map_apply hem hCm, hm]
    simp
  have hz : ∀ X, X ∉ A → G (w0 K * nn X * (nn Y * lv a b t * k)) = 0 := fun X hX => by
    by_contra h
    refine hX (hs _ k hk ?_)
    have := abs_le.1 (hR _ h)
    rw [he, hh_lv] at this
    linarith [this.1]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hfin : unipMeasure K (2 + 2) 2 A < ⊤ := by
    rw [hAm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top
  have := norm_setIntegral_le_of_norm_le_const (μ := unipMeasure K (2 + 2) 2) (f := fun X => G (w0 K * nn X * (nn Y * lv a b t * k))) hfin (fun X _ => hB _)
  rwa [Measure.real, hAm] at this

set_option synthInstance.maxHeartbeats 400000 in
private theorem fco {n : ℕ} : FirstCountableTopology (G1 K n) := by
  haveI := secondCountableTopology_normOneGL (K := K) (n := n)
  infer_instance

private theorem cont (G : G1 K (2 + 2) → ℂ) (B R : ℝ) (hG : Continuous G) (hB : ∀ g, ‖G g‖ ≤ B) (hR : ∀ g, G g ≠ 0 → |HH g| ≤ R) :
    Continuous fun x : G1 K (2 + 2) => ∫ X, G (w0 K * nn X * x) ∂unipMeasure K (2 + 2) 2 := by
  haveI : FirstCountableTopology (G1 K (2 + 2)) := fco
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G1 K (2 + 2))
  obtain ⟨R₀, hR₀⟩ := (hpSpec (K := K)).2.2.2.2 V hV
  obtain ⟨C, hC, hs⟩ := supp x₀ (R + R₀)
  have hc : ∀ x : G1 K (2 + 2), Continuous fun X : UPos (2 + 2) 2 → 𝔸[K] => G (w0 K * nn X * x) := fun x =>
    hG.comp ((continuous_const.mul nn_continuous).mul continuous_const)
  refine continuousAt_of_dominated (bound := C.indicator fun _ => B) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x => (hc x).aestronglyMeasurable
  · have ht : Tendsto (fun x : G1 K (2 + 2) => x₀⁻¹ * x) (𝓝 x₀) (𝓝 1) := by
      have : Continuous (fun x : G1 K (2 + 2) => x₀⁻¹ * x) := continuous_const.mul continuous_id
      have h := this.tendsto x₀
      rwa [inv_mul_cancel] at h
    filter_upwards [ht hV1] with x hx
    refine Eventually.of_forall fun X => ?_
    by_cases hX : X ∈ C
    · rw [Set.indicator_of_mem hX]
      exact hB _
    · rw [Set.indicator_of_notMem hX]
      by_contra hne
      have h0 : G (w0 K * nn X * x) ≠ 0 := fun h => hne (by rw [h, norm_zero])
      refine hX (hs X ?_)
      have h1 := abs_le.1 (hR _ h0)
      have h2 := abs_le.1 (hR₀ (w0 K * nn X * x₀) _ hx)
      rw [show w0 K * nn X * x₀ * (x₀⁻¹ * x) = w0 K * nn X * x by group] at h2
      linarith [h1.1, h2.2]
  · exact (integrable_indicator_iff hC.isClosed.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)
  · refine Eventually.of_forall fun X => ?_
    exact (hG.comp (continuous_const.mul continuous_id)).continuousAt

private theorem shift (G : G1 K (2 + 2) → ℂ) (Y : UPos (2 + 2) 2 → 𝔸[K]) (x : G1 K (2 + 2)) :
    ∫ X, G (w0 K * nn X * (nn Y * x)) ∂unipMeasure K (2 + 2) 2 = ∫ X, G (w0 K * nn X * x) ∂unipMeasure K (2 + 2) 2 := by
  have h : ∀ X, w0 K * nn X * (nn Y * x) = w0 K * nn (X + Y) * x := fun X => by
    rw [← nn_add]
    group
  simp_rw [h]
  exact integral_add_right_eq_self (fun X => G (w0 K * nn X * x)) Y

private theorem swap (G : G1 K (2 + 2) → ℂ) (m₁ m₂ : G1 K 2) (x : G1 K (2 + 2)) :
    ∫ X, G (w0 K * nn X * (lv m₁ m₂ 0 * x)) ∂unipMeasure K (2 + 2) 2 =
      ∫ X, G (lv m₂ m₁ 0 * (w0 K * nn X * x)) ∂unipMeasure K (2 + 2) 2 := by
  obtain ⟨e, he, hm⟩ := adMeas m₁ m₂ 0
  have hw := (blkLaws (K := K)).2.2.2.2.2.2.2.2.2.1 m₁ m₂ 0
  rw [neg_zero] at hw
  have hm' : (unipMeasure K (2 + 2) 2).map e = unipMeasure K (2 + 2) 2 := by
    rw [hm]
    simp
  have h : ∀ X, w0 K * nn X * (lv m₁ m₂ 0 * x) = lv m₂ m₁ 0 * (w0 K * nn (e X) * x) := fun X => by
    calc w0 K * nn X * (lv m₁ m₂ 0 * x) = w0 K * (nn X * lv m₁ m₂ 0) * x := by group
      _ = (w0 K * lv m₁ m₂ 0) * nn (e X) * x := by rw [he]; group
      _ = lv m₂ m₁ 0 * (w0 K * nn (e X) * x) := by rw [hw]; group
  simp_rw [h]
  conv_rhs => rw [← hm']
  exact (e.toHomeomorph.measurableEmbedding.integral_map (fun X => G (lv m₂ m₁ 0 * (w0 K * nn X * x)))).symm

private theorem aeKG (D : TypeDat K (2 + 2)) : ∀ᵐ k ∂D.ν, k ∈ KG K (2 + 2) := by
  obtain ⟨O, -, hOU⟩ := D.isOpen
  filter_upwards [D.supp] with k hk
  exact ((hOU k).1 hk).2

set_option synthInstance.maxHeartbeats 400000 in
private theorem fixL (D : TypeDat K (2 + 2)) (w : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ) (hwc : Continuous w) (hfc : Continuous f)
    (hfix : D.Fix f) (B R : ℝ) (hB : ∀ g, ‖w (HH g) * f g‖ ≤ B) (hR : ∀ g, w (HH g) * f g ≠ 0 → |HH g| ≤ R)
    (x : G1 K (2 + 2)) :
    ∫ k, D.e k * ∫ X, w (HH (w0 K * nn X * (x * k))) * f (w0 K * nn X * (x * k)) ∂unipMeasure K (2 + 2) 2 ∂D.ν =
      ∫ X, w (HH (w0 K * nn X * x)) * f (w0 K * nn X * x) ∂unipMeasure K (2 + 2) 2 := by
  haveI := D.prob
  obtain ⟨h1, h2, h3, hHc, h5⟩ := hpSpec (K := K)
  obtain ⟨C, hC, hs⟩ := supp x R
  obtain ⟨G, hG⟩ : ∃ G : G1 K (2 + 2) → ℂ, G = fun g => w (HH g) * f g := ⟨_, rfl⟩
  have hGc : Continuous G := by
    rw [hG]
    exact (hwc.comp hHc).mul hfc
  have hKG := aeKG D
  obtain ⟨Be, hBe⟩ : ∃ Be : ℝ, ∀ k ∈ KG K (2 + 2), ‖D.e k‖ ≤ Be := by
    obtain ⟨Be, hBe⟩ := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1.exists_bound_of_continuousOn D.cont.continuousOn
    exact ⟨Be, hBe⟩
  have hz : ∀ k ∈ KG K (2 + 2), ∀ X, X ∉ C → G (w0 K * nn X * x * k) = 0 := fun k hk X hX => by
    by_contra h
    refine hX (hs X ?_)
    have := abs_le.1 (hR _ (by simpa only [hG] using h))
    rw [(h2 k hk).2] at this
    linarith [this.1]
  have hz0 : ∀ X, X ∉ C → G (w0 K * nn X * x) = 0 := fun X hX => by
    have := hz 1 (one_mem _) X hX
    rwa [mul_one] at this
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = (unipMeasure K (2 + 2) 2).restrict C := ⟨_, rfl⟩
  haveI : IsFiniteMeasure lam := by
    rw [hlam]
    exact ⟨by simpa using hC.measure_lt_top⟩
  have e1 : ∫ k, D.e k * ∫ X, w (HH (w0 K * nn X * (x * k))) * f (w0 K * nn X * (x * k)) ∂unipMeasure K (2 + 2) 2 ∂D.ν =
      ∫ k, ∫ X, D.e k * G (w0 K * nn X * x * k) ∂lam ∂D.ν := by
    refine integral_congr_ae ?_
    filter_upwards [hKG] with k hk
    rw [integral_const_mul, hlam, setIntegral_eq_integral_of_forall_compl_eq_zero (hz k hk), hG]
    simp only [mul_assoc]
  have hcont : Continuous fun p : G1 K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K]) => D.e p.1 * G (w0 K * nn p.2 * x * p.1) :=
    (D.cont.comp continuous_fst).mul (hGc.comp
      (((continuous_const.mul (nn_continuous.comp continuous_snd)).mul continuous_const).mul continuous_fst))
  have hint : Integrable (Function.uncurry fun (k : G1 K (2 + 2)) (X : UPos (2 + 2) 2 → 𝔸[K]) => D.e k * G (w0 K * nn X * x * k))
      (D.ν.prod lam) := by
    refine Integrable.mono' (integrable_const (Be * B)) hcont.aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hKG] with p hp
    have hBG : ‖G (w0 K * nn p.2 * x * p.1)‖ ≤ B := by
      rw [hG]
      exact hB _
    rw [Function.uncurry_apply_pair, norm_mul]
    exact mul_le_mul (hBe _ hp) hBG (norm_nonneg _) ((norm_nonneg _).trans (hBe _ hp))
  rw [e1, integral_integral_swap hint]
  have e3 : ∀ X, ∫ k, D.e k * G (w0 K * nn X * x * k) ∂D.ν = G (w0 K * nn X * x) := fun X => by
    have : ∫ k, D.e k * G (w0 K * nn X * x * k) ∂D.ν =
        ∫ k, w (HH (w0 K * nn X * x)) * (D.e k * f (w0 K * nn X * x * k)) ∂D.ν := by
      refine integral_congr_ae ?_
      filter_upwards [hKG] with k hk
      rw [hG]
      simp only [(h2 k hk).2]
      ring
    rw [this, integral_const_mul, hfix, hG]
  simp_rw [e3]
  rw [hlam, setIntegral_eq_integral_of_forall_compl_eq_zero hz0, hG]

private theorem slice (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ : Submodule ℂ (L2 μ₂)) (hτ : IsClosed (τ : Set (L2 μ₂)))
    (G : G1 K (2 + 2) → ℂ) (B R : ℝ) (hG : Continuous G) (hB : ∀ g, ‖G g‖ ≤ B) (hR : ∀ g, G g ≠ 0 → |HH g| ≤ R)
    (hrat : ∀ γ ∈ PK K, ∀ g, G (γ * g) = G g) (L : G1 K 2 → G1 K (2 + 2)) (hL : Continuous L)
    (hLγ : ∀ γ ∈ Gam K 2, ∀ m, ∃ δ ∈ PK K, L (γ * m) = δ * L m) (hLH : ∀ m y, HH (L m * y) = HH y)
    (hrep : ∀ y, ∃ v ∈ τ, Reps μ₂ v fun m => G (L m * y)) (x : G1 K (2 + 2)) :
    ∃ v ∈ τ, Reps μ₂ v fun m => ∫ X, G (L m * (w0 K * nn X * x)) ∂unipMeasure K (2 + 2) 2 := by
  obtain ⟨C, hC, hs⟩ := supp x R
  haveI : IsFiniteMeasure ((unipMeasure K (2 + 2) 2).restrict C) := ⟨by simpa using hC.measure_lt_top⟩
  have hz : ∀ m, ∀ X, X ∉ C → G (L m * (w0 K * nn X * x)) = 0 := fun m X hX => by
    by_contra h
    refine hX (hs X ?_)
    have := abs_le.1 (hR _ h)
    rw [hLH] at this
    linarith [this.1]
  have := UpperTheory.reps_integral_mem_closed_submodule μ₂ τ hτ (UPos (2 + 2) 2 → 𝔸[K]) ((unipMeasure K (2 + 2) 2).restrict C)
    (fun X m => G (L m * (w0 K * nn X * x)))
    (hG.comp ((hL.comp continuous_snd).mul
      ((continuous_const.mul (nn_continuous.comp continuous_fst)).mul continuous_const)))
    ⟨B, fun _ _ => hB _⟩
    (fun X γ hγ m => by
      obtain ⟨δ, hδ, h⟩ := hLγ γ hγ m
      rw [h, mul_assoc, hrat δ hδ])
    (fun X => hrep _)
  simpa only [setIntegral_eq_integral_of_forall_compl_eq_zero (hz _)] using this

private theorem lvc₂ (a : G1 K 2) : Continuous fun m : G1 K 2 => lv a m 0 := by
  have h : Continuous fun m : G1 K 2 => ((a, m, 0) : G1 K 2 × G1 K 2 × ℝ) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have h2 := (blkLaws (K := K)).2.2.2.1.comp' h
  exact h2.congr fun m => rfl

private theorem lvc₁ (a : G1 K 2) : Continuous fun m : G1 K 2 => lv m a 0 := by
  have h : Continuous fun m : G1 K 2 => ((m, a, 0) : G1 K 2 × G1 K 2 × ℝ) :=
    continuous_id.prodMk continuous_const
  have h2 := (blkLaws (K := K)).2.2.2.1.comp' h
  simpa only [Function.comp_def] using h2

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Cell

set_option maxHeartbeats 1000000 in
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Cell in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.intertw :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ →
      ∀ (f : G1 K (2 + 2) → ℂ) (β : ℝ → ℂ) (s : ℝ), IsSec τ₁ τ₂ f → D.Fix f → Continuous β → HasCompactSupport β →
        IsSec τ₂ τ₁ (fun g => ∫ X, bf β f (w0 K * nn X * (lv 1 1 (s - HH g) * g)) ∂unipMeasure K (2 + 2) 2) ∧
        D.Fix fun g => ∫ X, bf β f (w0 K * nn X * (lv 1 1 (s - HH g) * g)) ∂unipMeasure K (2 + 2) 2 := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ D h₁ h₂ f β s hs hD hβ hc
  have hS := secFun μ₂ τ₁ τ₂ D h₁ h₂ f hs hD
  obtain ⟨hP, ⟨R, hR⟩, -⟩ := bfFun f β hS hβ hc
  obtain ⟨B, hB⟩ := hP.bdd
  have hsl : Slices τ₁ τ₂ f := ((secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hD).1 hs).2.2.2.2
  obtain ⟨-, hmul, -, hlc, -⟩ := blkLaws (K := K)
  obtain ⟨-, h2, -, hHc, -⟩ := hpSpec (K := K)
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℂ, w = fun t => β t * Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * t : ℝ) : ℂ) := ⟨_, rfl⟩
  have hbf : ∀ g, bf β f g = w (HH g) * f g := fun g => by rw [hw]; rfl
  have hb2 : bf β f = fun g => w (HH g) * f g := funext hbf
  have hwc : Continuous w := by
    rw [hw]
    exact hβ.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  obtain ⟨T, hT⟩ : ∃ T : G1 K (2 + 2) → G1 K (2 + 2), T = fun g => lv 1 1 (s - HH g) * g := ⟨_, rfl⟩
  have hTc : Continuous T := by
    rw [hT]
    exact (hlc.comp (continuous_const.prodMk (continuous_const.prodMk (continuous_const.sub hHc)))).mul continuous_id
  have hTH : ∀ g, HH (T g) = s := fun g => by
    rw [hT]
    beta_reduce
    rw [hh_lv]
    ring
  have hTk : ∀ g, ∀ k ∈ KG K (2 + 2), T (g * k) = T g * k := fun g k hk => by
    rw [hT]
    beta_reduce
    rw [(h2 k hk).2 g, mul_assoc]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G1 K (2 + 2) → ℂ, Φ = fun x => ∫ X, bf β f (w0 K * nn X * x) ∂unipMeasure K (2 + 2) 2 := ⟨_, rfl⟩
  have hF : (fun g => ∫ X, bf β f (w0 K * nn X * (lv 1 1 (s - HH g) * g)) ∂unipMeasure K (2 + 2) 2) = fun g => Φ (T g) := by
    rw [hΦ, hT]
  rw [hF]
  have hfix : D.Fix fun g => Φ (T g) := fun g => by
    have h := fixL D w f hwc hS.cont hD B R (fun g => by rw [← hbf]; exact hB g) (fun g hg => hR g (by rwa [hbf])) (T g)
    show ∫ k, D.e k * Φ (T (g * k)) ∂D.ν = Φ (T g)
    simp only [hΦ, hb2]
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [aeKG D] with k hk
    rw [hTk g k hk]
  have hP₁ : ∀ γ ∈ Gam K 2, lv γ 1 0 ∈ PK K := fun γ hγ =>
    (pkLaws (K := K)).2.1 _ |>.2 ⟨0, ⟨γ, hγ⟩, 1, by
      rw [show nn (0 : unipLattice K (2 + 2) 2).1 = 1 from unipOne_zero 2, one_mul]
      rfl⟩
  have hP₂ : ∀ γ ∈ Gam K 2, lv 1 γ 0 ∈ PK K := fun γ hγ =>
    (pkLaws (K := K)).2.1 _ |>.2 ⟨0, 1, ⟨γ, hγ⟩, by
      rw [show nn (0 : unipLattice K (2 + 2) 2).1 = 1 from unipOne_zero 2, one_mul]
      rfl⟩
  refine ⟨(secCrit μ₂ τ₂ τ₁ D h₂ h₁ _ hfix).2 ⟨?_, ?_, ?_, ?_, ?_⟩, hfix⟩
  · have hΦc : Continuous Φ := by
      rw [hΦ]
      exact cont (bf β f) B R hP.cont hB hR
    exact hΦc.comp hTc
  · obtain ⟨M, hM⟩ := bd (bf β f) B R hB hR s
    refine ⟨M, fun g => ?_⟩
    rw [hΦ]
    exact hM _ (hTH g)
  · intro Y g
    show Φ (T (nn Y * g)) = Φ (T g)
    obtain ⟨e, he, -⟩ := adMeas (1 : G1 K 2) 1 (s - HH g)
    have h : T (nn Y * g) = nn (e.symm Y) * T g := by
      rw [hT]
      beta_reduce
      rw [hh_nn, ← mul_assoc, ← mul_assoc, he, e.apply_symm_apply]
    rw [h, hΦ]
    exact shift _ _ _
  · intro t g
    show Φ (T (lv 1 1 t * g)) = Φ (T g)
    have h : T (lv 1 1 t * g) = T g := by
      rw [hT]
      beta_reduce
      rw [hh_lv, ← mul_assoc, hmul, mul_one, show s - (t + HH g) + t = s - HH g by ring]
    rw [h]
  · intro g
    have key : ∀ m₁ m₂ : G1 K 2, Φ (T (lv m₁ m₂ 0 * g)) =
        ∫ X, bf β f (lv m₂ m₁ 0 * (w0 K * nn X * T g)) ∂unipMeasure K (2 + 2) 2 := fun m₁ m₂ => by
      have h : T (lv m₁ m₂ 0 * g) = lv m₁ m₂ 0 * T g := by
        rw [hT]
        beta_reduce
        rw [hh_lv, zero_add, ← mul_assoc, ← mul_assoc, hmul, hmul, one_mul, one_mul, mul_one, mul_one, add_zero, zero_add]
      rw [h, hΦ]
      exact swap _ _ _ _
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · have := slice μ₂ τ₂ h₂.closed (bf β f) B R hP.cont hB hR hP.rat (fun m => lv m₂ m 0)
        (lvc₂ m₂)
        (fun γ hγ m => ⟨lv 1 γ 0, hP₂ γ hγ, by
          beta_reduce
          rw [hmul, one_mul, add_zero]⟩)
        (fun m y => (hh_lv m₂ m 0 y).trans (zero_add _))
        (fun y => by
          obtain ⟨v, hv, hr⟩ := (hsl y).2 m₂
          refine ⟨w (HH y) • v, τ₂.smul_mem _ hv, ?_⟩
          filter_upwards [(quasiMeasurePreserving_mk (Gam K 2) μ₂).ae (Lp.coeFn_smul (w (HH y)) v), hr] with m e1 e2
          rw [e1, Pi.smul_apply, e2, hbf, hh_lv, zero_add, smul_eq_mul])
        (T g)
      simpa only [key] using this
    · have := slice μ₂ τ₁ h₁.closed (bf β f) B R hP.cont hB hR hP.rat (fun m => lv m m₁ 0)
        (lvc₁ m₁)
        (fun γ hγ m => ⟨lv γ 1 0, hP₁ γ hγ, by
          beta_reduce
          rw [hmul, one_mul, add_zero]⟩)
        (fun m y => (hh_lv m m₁ 0 y).trans (zero_add _))
        (fun y => by
          obtain ⟨v, hv, hr⟩ := (hsl y).1 m₁
          refine ⟨w (HH y) • v, τ₁.smul_mem _ hv, ?_⟩
          filter_upwards [(quasiMeasurePreserving_mk (Gam K 2) μ₂).ae (Lp.coeFn_smul (w (HH y)) v), hr] with m e1 e2
          rw [e1, Pi.smul_apply, e2, hbf, hh_lv, zero_add, smul_eq_mul])
        (T g)
      simpa only [key] using this
