import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Master
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SwapInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LongCell
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem five {M₁ M₂ T Kc U : Type} [MeasurableSpace M₁] [MeasurableSpace M₂] [MeasurableSpace T] [MeasurableSpace Kc]
    [MeasurableSpace U] (a₁ : Measure M₁) (a₂ : Measure M₂) (τ : Measure T) (κ : Measure Kc) (ν : Measure U)
    [SFinite a₁] [SFinite a₂] [SFinite τ] [SFinite κ] [SFinite ν] (G : M₁ × M₂ × T × Kc × U → ℂ)
    (h : Integrable G (a₁.prod (a₂.prod (τ.prod (κ.prod ν))))) :
    ∫ p, G p ∂(a₁.prod (a₂.prod (τ.prod (κ.prod ν)))) =
      ∫ m₁, ∫ m₂, ∫ t, ∫ k, ∫ X, G (m₁, m₂, t, k, X) ∂ν ∂κ ∂τ ∂a₂ ∂a₁ := by
  rw [integral_prod _ h]
  refine integral_congr_ae ?_
  filter_upwards [h.prod_right_ae] with m₁ h1
  rw [integral_prod _ h1]
  refine integral_congr_ae ?_
  filter_upwards [h1.prod_right_ae] with m₂ h2
  rw [integral_prod _ h2]
  refine integral_congr_ae ?_
  filter_upwards [h2.prod_right_ae] with t h3
  rw [integral_prod _ h3]

private theorem swap {M Z : Type} [MeasurableSpace M] [MeasurableSpace Z] (a : Measure M) (ζ : Measure Z) [IsFiniteMeasure a]
    [SFinite ζ] (u : Z → ℂ) (hu : Integrable u ζ) (b : M → M → Z → ℂ)
    (hb : StronglyMeasurable fun p : (M × M) × Z => b p.1.1 p.1.2 p.2) (C : ℝ) (hC : ∀ x y z, ‖b x y z‖ ≤ C) :
    (∀ x y, Integrable (fun z => u z * b x y z) ζ) ∧
    Integrable (fun m : M × M => ∫ z, u z * b m.1 m.2 z ∂ζ) (a.prod a) ∧
    Integrable (fun z => u z * ∫ x, ∫ y, b x y z ∂a ∂a) ζ ∧
    ∫ m : M × M, ∫ z, u z * b m.1 m.2 z ∂ζ ∂(a.prod a) = ∫ z, u z * ∫ x, ∫ y, b x y z ∂a ∂a ∂ζ := by
  have h0 : Integrable (fun p : (M × M) × Z => u p.2 * b p.1.1 p.1.2 p.2) ((a.prod a).prod ζ) :=
    (hu.comp_snd (a.prod a)).mul_bdd hb.aestronglyMeasurable (Eventually.of_forall fun p => hC _ _ _)
  have h1 : ∀ z, ∫ m : M × M, u z * b m.1 m.2 z ∂(a.prod a) = u z * ∫ x, ∫ y, b x y z ∂a ∂a := by
    intro z
    rw [integral_const_mul, integral_prod]
    exact Integrable.of_bound (hb.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
      (Eventually.of_forall fun p => hC _ _ _)
  refine ⟨fun x y => ?_, h0.integral_prod_left, ?_, ?_⟩
  · exact hu.mul_bdd (hb.comp_measurable (g := fun z => ((x, y), z)) (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun p => hC _ _ _)
  · simpa only [h1] using h0.integral_prod_right
  · rw [integral_integral_swap (f := fun (m : M × M) z => u z * b m.1 m.2 z) h0]
    simp only [h1]

private theorem two {M T Kc U : Type} [MeasurableSpace M] [MeasurableSpace T] [MeasurableSpace Kc]
    [MeasurableSpace U] (a : Measure M) (τ : Measure T) (κ : Measure Kc) (ν : Measure U)
    [IsFiniteMeasure a] [SFinite τ] [SFinite κ] [SFinite ν]
    (u : T × Kc → ℂ) (hu : Integrable u (τ.prod κ)) (b : M → M → T × Kc → ℂ)
    (hb : StronglyMeasurable fun p : (M × M) × T × Kc => b p.1.1 p.1.2 p.2) (C : ℝ) (hC : ∀ x y z, ‖b x y z‖ ≤ C)
    (u' : (T × Kc) × U → ℂ) (hu' : Integrable u' ((τ.prod κ).prod ν)) (b' : M → M → (T × Kc) × U → ℂ)
    (hb' : StronglyMeasurable fun p : (M × M) × (T × Kc) × U => b' p.1.1 p.1.2 p.2) (C' : ℝ) (hC' : ∀ x y z, ‖b' x y z‖ ≤ C') :
    ∫ x, ∫ y, ∫ t, ∫ k, (u (t, k) * b x y (t, k) + ∫ X, u' ((t, k), X) * b' x y ((t, k), X) ∂ν) ∂κ ∂τ ∂a ∂a =
      ∫ t, ∫ k, u (t, k) * ∫ x, ∫ y, b x y (t, k) ∂a ∂a ∂κ ∂τ +
        ∫ t, ∫ k, ∫ X, u' ((t, k), X) * ∫ x, ∫ y, b' x y ((t, k), X) ∂a ∂a ∂ν ∂κ ∂τ := by
  obtain ⟨p1, p2, p3, p4⟩ := swap a _ u hu b hb C hC
  obtain ⟨q1, q2, q3, q4⟩ := swap a _ u' hu' b' hb' C' hC'
  have h1 : ∀ x y, ∫ t, ∫ k, (u (t, k) * b x y (t, k) + ∫ X, u' ((t, k), X) * b' x y ((t, k), X) ∂ν) ∂κ ∂τ =
      ∫ z, u z * b x y z ∂(τ.prod κ) + ∫ z, u' z * b' x y z ∂((τ.prod κ).prod ν) := by
    intro x y
    rw [integral_prod _ (q1 x y), ← integral_add (p1 x y) (q1 x y).integral_prod_left]
    exact (integral_prod _ ((p1 x y).add (q1 x y).integral_prod_left)).symm
  simp only [h1]
  refine (integral_prod (fun m : M × M => ∫ z, u z * b m.1 m.2 z ∂(τ.prod κ) +
    ∫ z, u' z * b' m.1 m.2 z ∂((τ.prod κ).prod ν)) (p2.add q2)).symm.trans ?_
  rw [integral_add p2 q2, p4, q4, integral_prod _ p3, integral_prod _ q3,
    integral_prod _ q3.integral_prod_left]

private theorem twoC {M Kc U : Type} [MeasurableSpace M] [MeasurableSpace Kc] [MeasurableSpace U]
    [TopologicalSpace M] [TopologicalSpace Kc] [TopologicalSpace U] [BorelSpace M] [BorelSpace Kc] [BorelSpace U]
    [SecondCountableTopology M] [SecondCountableTopology Kc] [SecondCountableTopology U]
    (a : Measure M) (κ : Measure Kc) (ν : Measure U)
    [IsFiniteMeasure a] [IsFiniteMeasure κ] [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    (u : ℝ → ℂ) (hu : Continuous u) (hus : HasCompactSupport u) (b : M → M → Kc → ℂ)
    (hb : Continuous fun p : (M × M) × Kc => b p.1.1 p.1.2 p.2) (C : ℝ) (hC : ∀ x y z, ‖b x y z‖ ≤ C)
    (u' : ℝ → Kc → U → ℂ) (hu' : Continuous fun p : (ℝ × Kc) × U => u' p.1.1 p.1.2 p.2)
    (hus' : HasCompactSupport fun p : (ℝ × Kc) × U => u' p.1.1 p.1.2 p.2) (b' : M → M → Kc → U → ℂ)
    (hb' : Continuous fun p : (M × M) × Kc × U => b' p.1.1 p.1.2 p.2.1 p.2.2) (C' : ℝ) (hC' : ∀ x y k X, ‖b' x y k X‖ ≤ C') :
    ∫ x, ∫ y, ∫ t, ∫ k, (u t * b x y k + ∫ X, u' t k X * b' x y k X ∂ν) ∂κ ∂volume ∂a ∂a =
      (∫ t, u t) * ∫ k, ∫ x, ∫ y, b x y k ∂a ∂a ∂κ +
        ∫ t, ∫ k, ∫ X, u' t k X * ∫ x, ∫ y, b' x y k X ∂a ∂a ∂ν ∂κ := by
  have h := two a volume κ ν (fun p => u p.1) ((hu.integrable_of_hasCompactSupport hus).comp_fst κ)
    (fun x y p => b x y p.2) (hb.comp (continuous_fst.prodMk continuous_snd.snd)).stronglyMeasurable C (fun _ _ _ => hC _ _ _)
    (fun p => u' p.1.1 p.1.2 p.2) (hu'.integrable_of_hasCompactSupport hus') (fun x y p => b' x y p.1.2 p.2)
    (hb'.comp (continuous_fst.prodMk (continuous_snd.fst.snd.prodMk continuous_snd.snd))).stronglyMeasurable C'
    (fun _ _ _ => hC' _ _ _ _)
  refine h.trans ?_
  simp only [integral_const_mul, integral_mul_const]

private theorem bf_lv {K : Type} [Field K] [NumberField K] {f : G1 K (2 + 2) → ℂ} (hf : SFun f) (β : ℝ → ℂ) (x y : G1 K 2) (t : ℝ)
    (g : G1 K (2 + 2)) :
    bf β f (lv x y t * g) = β (t + HH g) * Complex.exp (2 * ((t : ℂ) + (HH g : ℂ))) * f (lv x y 0 * g) := by
  have h1 : HP 2 2 (lv x y t * g) = t + HH g := by
    have := (hpSpec (K := K)).1 0 x y t g
    rwa [show nn (0 : UPos (2 + 2) 2 → 𝔸[K]) = 1 from unipOne_zero 2, one_mul] at this
  have h2 : f (lv x y t * g) = f (lv x y 0 * g) := by
    rw [← hf.ray t (lv x y 0 * g), ← mul_assoc, (blkLaws (K := K)).2.1, one_mul, one_mul, add_zero]
  rw [bf, h1, h2]
  congr 3
  push_cast
  ring

private theorem inner_eq {K : Type} [Field K] [NumberField K] {f f' : G1 K (2 + 2) → ℂ} {β β' : ℝ → ℂ} (hf : SFun f) (hf' : SFun f')
    (hβ' : Continuous β') (hβs' : HasCompactSupport β') (x y : G1 K 2) (t : ℝ) (k : G1 K (2 + 2)) (hk : k ∈ KG K (2 + 2)) :
    (Real.exp (-4 * t) : ℂ) * ∫ X in unipFundamentalDomain K (2 + 2) 2,
      conj (bf β f (nn X * lv x y t * k)) * th (bf β' f') (nn X * lv x y t * k) ∂unipMeasure K (2 + 2) 2 =
    (volN K * (conj (β t) * β' t)) * (conj (f (lv x y 0 * k)) * f' (lv x y 0 * k)) +
      ∫ X, (conj (β t) * β' (HH (w0 K * nn X * k) - t) * Complex.exp (2 * (HH (w0 K * nn X * k) : ℂ))) *
        (conj (f (lv x y 0 * k)) * f' (lv y x 0 * (w0 K * nn X * k))) ∂unipMeasure K (2 + 2) 2 := by
  obtain ⟨hP', hB', -⟩ := bfFun f' β' hf' hβ' hβs'
  have hH : HH k = 0 := ((hpSpec (K := K)).2.1 k hk).1
  have h1 : ∀ X, bf β f (nn X * lv x y t * k) = β t * Complex.exp (2 * (t : ℂ)) * f (lv x y 0 * k) := by
    intro X
    have h : bf β f (nn X * lv x y t * k) = bf β f (lv x y t * k) := by
      have h0 : HP 2 2 (nn X * lv x y t * k) = HP 2 2 (lv x y t * k) := by
        have := (hpSpec (K := K)).1 X 1 1 0 (lv x y t * k)
        rwa [(blkLaws (K := K)).2.2.1, mul_one, zero_add, ← mul_assoc] at this
      rw [bf, bf, h0, mul_assoc (nn X), hf.unip]
    rw [h, bf_lv hf, hH]
    simp
  obtain ⟨e, he, hm⟩ := adMeas x y t
  have h2 : ∫ X, bf β' f' (w0 K * nn X * (lv x y t * k)) ∂unipMeasure K (2 + 2) 2 =
      (Real.exp (4 * t) : ℂ) * ∫ X, bf β' f' (lv y x (-t) * (w0 K * nn X * k)) ∂unipMeasure K (2 + 2) 2 := by
    have h3 := integral_map_equiv (μ := unipMeasure K (2 + 2) 2) e.toHomeomorph.toMeasurableEquiv
      (fun X => bf β' f' (lv y x (-t) * (w0 K * nn X * k)))
    have h4 : (e.toHomeomorph.toMeasurableEquiv : _ → _) = e := rfl
    rw [h4, hm, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul] at h3
    rw [h3]
    refine integral_congr_ae (Eventually.of_forall fun X => congrArg (bf β' f') ?_)
    show w0 K * nn X * (lv x y t * k) = lv y x (-t) * (w0 K * nn (e X) * k)
    rw [← mul_assoc, mul_assoc (w0 K), he, ← mul_assoc, (blkLaws (K := K)).2.2.2.2.2.2.2.2.2.1]
    simp only [mul_assoc]
  simp only [h1]
  simp only [mul_assoc (nn _)]
  rw [integral_const_mul, (thCt _ hP' hB' (lv x y t * k)).2.2.2, h2, bf_lv hf', hH]
  simp only [bf_lv hf']
  have hc : conj (Complex.exp (2 * (t : ℂ))) = Complex.exp (2 * (t : ℂ)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, map_ofNat]
  have e1 : (Real.exp (-4 * t) : ℂ) * Complex.exp (2 * (t : ℂ)) * Complex.exp (2 * (t : ℂ)) = 1 := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1; push_cast; ring
  have e2 : ∀ s : ℝ, (Real.exp (-4 * t) : ℂ) * Complex.exp (2 * (t : ℂ)) * (Real.exp (4 * t) : ℂ) *
      Complex.exp (2 * (((-t : ℝ) : ℂ) + s)) = Complex.exp (2 * (s : ℂ)) := by
    intro s
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [mul_add, mul_add, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  simp only [map_mul, hc, add_zero, Complex.ofReal_zero]
  refine congrArg₂ (· + ·) ?_ ?_
  · linear_combination (volN K * (conj (β t) * β' t)) * (conj (f (lv x y 0 * k)) * f' (lv x y 0 * k)) * e1
  · refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    beta_reduce
    rw [neg_add_eq_sub, ← e2 (HH (w0 K * nn X * k))]
    ring

private theorem cont_lv {K : Type} [Field K] [NumberField K] : Continuous fun p : G1 K 2 × G1 K 2 => lv p.1 p.2 0 :=
  (blkLaws (K := K)).2.2.2.1.comp (f := fun p : G1 K 2 × G1 K 2 => (p.1, p.2, (0 : ℝ)))
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

private theorem cont_w {K : Type} [Field K] [NumberField K] :
    Continuous fun p : KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K]) => w0 K * nn p.2 * p.1.1 :=
  (continuous_const.mul ((continuous_unipOne 2).comp continuous_snd)).mul (continuous_subtype_val.comp continuous_fst)

private theorem cont_b {K Z : Type} [Field K] [NumberField K] [TopologicalSpace Z] {f f' : G1 K (2 + 2) → ℂ} (hf : Continuous f)
    (hf' : Continuous f') {i j : Z → G1 K (2 + 2)} (hi : Continuous i) (hj : Continuous j) :
    Continuous (fun p : (G1 K 2 × G1 K 2) × Z => conj (f (lv p.1.1 p.1.2 0 * i p.2)) * f' (lv p.1.1 p.1.2 0 * j p.2)) ∧
    Continuous fun p : (G1 K 2 × G1 K 2) × Z => conj (f (lv p.1.1 p.1.2 0 * i p.2)) * f' (lv p.1.2 p.1.1 0 * j p.2) := by
  have h1 : Continuous fun p : (G1 K 2 × G1 K 2) × Z => lv p.1.1 p.1.2 0 := cont_lv.comp continuous_fst
  have h2 : Continuous fun p : (G1 K 2 × G1 K 2) × Z => lv p.1.2 p.1.1 0 :=
    cont_lv.comp (f := fun p : (G1 K 2 × G1 K 2) × Z => (p.1.2, p.1.1)) (continuous_fst.snd.prodMk continuous_fst.fst)
  have h3 := Complex.continuous_conj.comp' (hf.comp' (h1.mul (hi.comp' continuous_snd)))
  exact ⟨h3.mul (hf'.comp' (h1.mul (hj.comp' continuous_snd))), h3.mul (hf'.comp' (h2.mul (hj.comp' continuous_snd)))⟩

private theorem cont_u {Z U : Type} [TopologicalSpace Z] [TopologicalSpace U] [T2Space Z] [T2Space U] [CompactSpace Z]
    {β β' : ℝ → ℂ} (hβ : Continuous β) (hβs : HasCompactSupport β) (hβ' : Continuous β') (hβs' : HasCompactSupport β')
    (h : Z → U → ℝ) (hh : Continuous fun p : Z × U => h p.1 p.2)
    (hS : ∀ R : ℝ, ∃ S : Set U, IsCompact S ∧ ∀ X k, -R ≤ h k X → X ∈ S) :
    Continuous (fun p : (ℝ × Z) × U => conj (β p.1.1) * β' (h p.1.2 p.2 - p.1.1) * Complex.exp (2 * (h p.1.2 p.2 : ℂ))) ∧
    HasCompactSupport fun p : (ℝ × Z) × U => conj (β p.1.1) * β' (h p.1.2 p.2 - p.1.1) * Complex.exp (2 * (h p.1.2 p.2 : ℂ)) := by
  have hH : Continuous fun p : (ℝ × Z) × U => h p.1.2 p.2 := hh.comp (continuous_fst.snd.prodMk continuous_snd)
  have ht : Continuous fun p : (ℝ × Z) × U => p.1.1 := continuous_fst.fst
  refine ⟨((Complex.continuous_conj.comp (hβ.comp ht)).mul (hβ'.comp (hH.sub ht))).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hH))), ?_⟩
  obtain ⟨R, hR⟩ := hβs.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R', hR'⟩ := hβs'.isCompact.isBounded.subset_closedBall 0
  obtain ⟨S, hS, hS'⟩ := hS (R + R')
  refine HasCompactSupport.intro ((hβs.isCompact.prod isCompact_univ).prod hS) fun p hp => ?_
  by_contra h0
  have h1 : p.1.1 ∈ tsupport β := subset_tsupport _ fun h1 => h0 (by simp only [h1, map_zero, zero_mul])
  have h2 : h p.1.2 p.2 - p.1.1 ∈ tsupport β' := subset_tsupport _ fun h1 => h0 (by simp only [h1, mul_zero, zero_mul])
  have h3 := hR h1
  have h4 := hR' h2
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at h3 h4
  exact hp ⟨⟨h1, mem_univ _⟩, hS' _ _ (by linarith [h3.1, h4.1])⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pairF :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (c : ℝ), Unf μ μ₂ κ c → ∀ (f f' : G1 K (2 + 2) → ℂ) (β β' : ℝ → ℂ), SFun f → SFun f' → Continuous β → HasCompactSupport β → Continuous β' → HasCompactSupport β' →
      ∀ v v' : L2 μ, Reps μ v (theta β f) → Reps μ v' (theta β' f') →
      ⟪v, v'⟫_ℂ = c * (volN K * (∫ t, conj (β t) * β' t) * (∫ k : KG K (2 + 2), pm μ₂ f f' k k ∂κ) +
        ∫ t : ℝ, ∫ k : KG K (2 + 2), ∫ X, conj (β t) * β' (HH (w0 K * nn X * k.1) - t) * Complex.exp (2 * (HH (w0 K * nn X * k.1) : ℂ)) *
          pw μ₂ f f' k (w0 K * nn X * k.1) ∂unipMeasure K (2 + 2) 2 ∂κ) := by
  intro K _ _ μ _ μ₂ _ κ _ c hU f f' β β' hf hf' hβ hβs hβ' hβs' v v' hv hv'
  obtain ⟨hP, hB, hD⟩ := bfFun f β hf hβ hβs
  obtain ⟨hP', hB', hD'⟩ := bfFun f' β' hf' hβ' hβs'
  obtain ⟨-, hc', hi', -⟩ := thBasic μ _ hP'.cont hP'.rat hB'
  obtain ⟨hI, hE⟩ := (master μ μ₂ κ c hU _ hP.cont hP.rat hB hD v v' hv).2.2 _ hc' hi' hv'
  haveI := isFiniteMeasure_quotientMeasure μ₂
  haveI : IsFiniteMeasure (fd μ₂) := isFiniteMeasure_restrict.2 (measure_fundamentalDomain_pos_lt_top (Gam K 2) μ₂).2.ne
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : IsFiniteMeasure κ := CompactSpace.isFiniteMeasure
  haveI : SecondCountableTopology (KG K (2 + 2)) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨C', hC'⟩ := hf'.bdd
  have hbd : ∀ g g', ‖conj (f g) * f' g'‖ ≤ C * C' := fun g g' => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg _).trans (hC g))
  obtain ⟨hu, hus⟩ := cont_u hβ hβs hβ' hβs' (fun (k : KG K (2 + 2)) X => HH (w0 K * nn X * k.1))
    ((hpSpec (K := K)).2.2.2.1.comp' cont_w) fun R => by
      obtain ⟨S, hS, hS'⟩ := (longCell (K := K)).2 R
      exact ⟨S, hS, fun X k => hS' X k.1 k.2⟩
  have hb := (cont_b hf.cont hf'.cont (Z := KG K (2 + 2)) continuous_subtype_val continuous_subtype_val).1
  have hb' := (cont_b hf.cont hf'.cont (Z := KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K]))
    (continuous_subtype_val.comp' continuous_fst) cont_w).2
  have key := twoC (fd μ₂) κ (unipMeasure K (2 + 2) 2) (fun t => volN K * (conj (β t) * β' t))
    (continuous_const.mul ((Complex.continuous_conj.comp hβ).mul hβ')) hβs'.mul_left.mul_left
    (fun x y k => conj (f (lv x y 0 * k.1)) * f' (lv x y 0 * k.1)) hb (C * C') (fun _ _ _ => hbd _ _)
    (fun t k X => conj (β t) * β' (HH (w0 K * nn X * k.1) - t) * Complex.exp (2 * (HH (w0 K * nn X * k.1) : ℂ))) hu hus
    (fun x y k X => conj (f (lv x y 0 * k.1)) * f' (lv y x 0 * (w0 K * nn X * k.1))) hb' (C * C') (fun _ _ _ _ => hbd _ _)
  rw [integral_const_mul] at key
  rw [hE, parM, five _ _ _ _ _ _ hI]
  refine congrArg (fun z : ℂ => c * z) (Eq.trans ?_ key)
  refine integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun y => ?_))
  beta_reduce
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun k => inner_eq hf hf' hβ' hβs' x y t k.1 k.2)
