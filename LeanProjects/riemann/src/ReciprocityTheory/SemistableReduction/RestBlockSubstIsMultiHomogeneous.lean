import ReciprocityTheory.SemistableReduction.AevalIsWeightedHomogeneous

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial

theorem sphereMeasure_isProbability {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (sphereProb n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold sphereProb
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (Metric.measure_ball_pos _ _ one_pos).ne'
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℂ (Fin n))).ne'
  · rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne

theorem blockSphereMeasure_isProbability {B n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (blockSphereProb B n) := by
  haveI := sphereMeasure_isProbability hn
  unfold blockSphereProb
  infer_instance

theorem eval_aeval_alt {σ τ : Type*} (v : σ → MvPolynomial τ ℂ) (x : τ → ℂ)
    (g : MvPolynomial σ ℂ) : eval x (aeval v g) = eval (fun i => eval x (v i)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, eval_X, hp]

theorem measurable_eval_blockCoords {B n : ℕ} (g : MvPolynomial (Fin B × Fin n) ℂ) :
    Measurable fun z : BlockSphere B n => eval (blockPoint z) g := by
  have hc : Continuous fun z : BlockSphere B n => blockPoint z :=
    continuous_pi fun p => (continuous_apply p.2).comp ((PiLp.continuous_ofLp 2 _).comp
      (continuous_subtype_val.comp (continuous_apply p.1)))
  exact ((MvPolynomial.continuous_eval g).comp hc).measurable

theorem isMultiHomogeneous_C_mul {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) : IsMultiHomogeneous a (C c * g) := by
  intro s hs
  rw [← MvPolynomial.smul_eq_C_mul] at hs
  exact hg s (MvPolynomial.support_smul hs)

theorem null_of_logBound {B n : ℕ} (hn : 0 < n) (hInt : SphereLogIntegrableStatement)
    (hbound : ∀ (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ) (u : BlockSphere B n),
      IsMultiHomogeneous a g → eval (blockPoint u) g ≠ 0 →
      Real.log ‖eval (blockPoint u) g‖ - (∑ b, (a b : ℝ)) / 2 * (harmonic (n - 1) : ℝ) ≤
        blockSphereMean B n g)
    (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ) (u : BlockSphere B n)
    (hg : IsMultiHomogeneous a g) (hu : eval (blockPoint u) g ≠ 0) :
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  classical
  haveI := blockSphereMeasure_isProbability (B := B) hn
  have hZm : MeasurableSet {z : BlockSphere B n | eval (blockPoint z) g = 0} :=
    measurableSet_eq_fun (measurable_eval_blockCoords g) measurable_const
  have hg0 : g ≠ 0 := by rintro rfl; exact hu (by simp)
  have hI := hInt B n a g hg0 hg
  have hmean : ∀ c : ℂ, c ≠ 0 → blockSphereMean B n (C c * g) = blockSphereMean B n g +
      (blockSphereProb B n).real {z | eval (blockPoint z) g = 0}ᶜ * Real.log ‖c‖ := by
    intro c hc
    have hpt : (fun z => Real.log ‖eval (blockPoint z) (C c * g)‖) = fun z =>
        Real.log ‖eval (blockPoint z) g‖ +
          {z : BlockSphere B n | eval (blockPoint z) g = 0}ᶜ.indicator (fun _ => Real.log ‖c‖) z := by
      funext z
      by_cases hz : eval (blockPoint z) g = 0
      · have hz' : z ∉ {z : BlockSphere B n | eval (blockPoint z) g = 0}ᶜ := fun h => h hz
        rw [Set.indicator_of_notMem hz', map_mul, hz, mul_zero, add_zero]
      · have hz' : z ∈ {z : BlockSphere B n | eval (blockPoint z) g = 0}ᶜ := hz
        rw [Set.indicator_of_mem hz', map_mul, eval_C, norm_mul,
          Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]
        ring
    unfold blockSphereMean
    rw [hpt, integral_add hI ((integrable_const _).indicator hZm.compl),
      integral_indicator_const _ hZm.compl, smul_eq_mul]
  by_contra hne
  have hP : 0 < (blockSphereProb B n).real {z | eval (blockPoint z) g = 0} :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hcompl : (blockSphereProb B n).real {z | eval (blockPoint z) g = 0}ᶜ =
      1 - (blockSphereProb B n).real {z | eval (blockPoint z) g = 0} := by
    simp only [Measure.real]
    rw [prob_compl_eq_one_sub hZm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  set P := (blockSphereProb B n).real {z | eval (blockPoint z) g = 0} with hPdef
  set M : ℝ := blockSphereMean B n g - Real.log ‖eval (blockPoint u) g‖ +
    (∑ b, (a b : ℝ)) / 2 * (harmonic (n - 1) : ℝ) with hM
  set c : ℂ := ((Real.exp ((M + 1) / P) : ℝ) : ℂ) with hcdef
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hlc : Real.log ‖c‖ = (M + 1) / P := by
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp]
  have hb := hbound a (C c * g) u (isMultiHomogeneous_C_mul hg c)
    (by rw [map_mul, eval_C]; exact mul_ne_zero hc hu)
  rw [hmean c hc, hcompl, map_mul, eval_C, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hu), hlc] at hb
  have h1 : P * ((M + 1) / P) = M + 1 := by field_simp
  have h2 : (1 - P) * ((M + 1) / P) = (M + 1) / P - (M + 1) := by rw [sub_mul, one_mul, h1]
  rw [h2] at hb
  linarith

def lh0First {B n : ℕ} (y : BlockSphere B n) : Fin (B + 1) × Fin n → MvPolynomial (Fin n) ℂ :=
  fun p => (Fin.cons (fun j => X j) (fun b j => C (blockPoint y (b, j))) :
    Fin (B + 1) → Fin n → MvPolynomial (Fin n) ℂ) p.1 p.2

def lh0Rest {B n : ℕ} (x : Fin n → ℂ) : Fin (B + 1) × Fin n → MvPolynomial (Fin B × Fin n) ℂ :=
  fun p => (Fin.cons (fun j => C (x j)) (fun b j => X (b, j)) :
    Fin (B + 1) → Fin n → MvPolynomial (Fin B × Fin n) ℂ) p.1 p.2

abbrev lh0Split (B n : ℕ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (B + 1) => UnitSphereC n) 0

theorem firstBlockSubst_eval {B n : ℕ} (x : UnitSphereC n) (y : BlockSphere B n) :
    (fun p => eval (spherePoint x) (lh0First y p)) =
      blockPoint ((lh0Split B n).symm (x, y)) := by
  funext ⟨b, j⟩
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  refine Fin.cases ?_ (fun b => ?_) b <;>
    simp [lh0First, blockPoint, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem restBlockSubst_eval {B n : ℕ} (x : UnitSphereC n) (y : BlockSphere B n) :
    (fun p => eval (blockPoint y) (lh0Rest (spherePoint x) p)) =
      blockPoint ((lh0Split B n).symm (x, y)) := by
  funext ⟨b, j⟩
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  refine Fin.cases ?_ (fun b => ?_) b <;>
    simp [lh0Rest, blockPoint, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem blockSplitEquiv_self {B n : ℕ} (u : BlockSphere (B + 1) n) :
    (lh0Split B n).symm (u 0, fun b => u b.succ) = u := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  funext i
  refine Fin.cases ?_ (fun b => ?_) i <;> simp [Fin.insertNthEquiv, Fin.insertNth_zero']

private theorem aeval_whom_lemma {σ τ : Type*} {M : Type*} [AddCommMonoid M] (w : τ → M)
    (v : σ → MvPolynomial τ ℂ) (d : σ → M) (hv : ∀ i, IsWeightedHomogeneous w (v i) (d i))
    (g : MvPolynomial σ ℂ) (m : M) (hg : ∀ s ∈ g.support, ∑ i ∈ s.support, s i • d i = m) :
    IsWeightedHomogeneous w (aeval v g) m := by
  classical
  rw [g.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_eq, ← hg s hs,
    ← zero_add (∑ i ∈ s.support, s i • d i), Finsupp.prod]
  exact (isWeightedHomogeneous_C w _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun i _ => (hv i).pow _)

theorem firstBlockSubst_isHomogeneous {B n : ℕ} {a : Fin (B + 1) → ℕ}
    {g : MvPolynomial (Fin (B + 1) × Fin n) ℂ} (hg : IsMultiHomogeneous a g)
    (y : BlockSphere B n) : (aeval (lh0First y) g).IsHomogeneous (a 0) := by
  classical
  refine aeval_whom_lemma 1 (lh0First y)
    (fun p => (Fin.cons 1 (fun _ => 0) : Fin (B + 1) → ℕ) p.1) ?_ g (a 0) ?_
  · rintro ⟨b, j⟩
    refine Fin.cases ?_ (fun b => ?_) b
    · simpa [lh0First] using isWeightedHomogeneous_X ℂ (1 : Fin n → ℕ) j
    · simpa [lh0First] using isWeightedHomogeneous_C (1 : Fin n → ℕ) (blockPoint y (b, j))
  · intro s hs
    rw [Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul], Fintype.sum_prod_type, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_eq_mul, mul_one, mul_zero,
      Finset.sum_const_zero, add_zero]
    exact hg s hs 0

theorem restBlockSubst_isMultiHomogeneous {B n : ℕ} {a : Fin (B + 1) → ℕ}
    {g : MvPolynomial (Fin (B + 1) × Fin n) ℂ} (hg : IsMultiHomogeneous a g) (x : Fin n → ℂ) :
    IsMultiHomogeneous (fun b => a b.succ) (aeval (lh0Rest x) g) := by
  classical
  have hW : IsWeightedHomogeneous (fun p : Fin B × Fin n => (Pi.single p.1 1 : Fin B → ℕ))
      (aeval (lh0Rest x) g) (fun b => a b.succ) := by
    refine aeval_whom_lemma _ (lh0Rest x)
      (fun p => (Fin.cons (0 : Fin B → ℕ) (fun b => Pi.single b 1) :
        Fin (B + 1) → Fin B → ℕ) p.1) ?_ g _ ?_
    · rintro ⟨b, j⟩
      refine Fin.cases ?_ (fun b => ?_) b
      · simpa [lh0Rest] using isWeightedHomogeneous_C
          (fun p : Fin B × Fin n => (Pi.single p.1 1 : Fin B → ℕ)) (x j)
      · simpa [lh0Rest] using isWeightedHomogeneous_X ℂ
          (fun p : Fin B × Fin n => (Pi.single p.1 1 : Fin B → ℕ)) (b, j)
    · intro s hs
      funext b
      rw [Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [Finsupp.notMem_support_iff.mp hi, zero_smul], Finset.sum_apply,
        Fintype.sum_prod_type, Fin.sum_univ_succ, ← hg s hs b.succ]
      simp only [Fin.cons_zero, Fin.cons_succ, smul_zero, Pi.zero_apply, Finset.sum_const_zero,
        zero_add]
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc
        simp [Pi.single_apply, Ne.symm hc]
      · simp
  intro s hs b
  have hb := congrFun (hW (MvPolynomial.mem_support_iff.mp hs)) b
  refine Eq.trans ?_ hb
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply,
    Finset.sum_subset (s₁ := s.support) (Finset.subset_univ _) fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul, Pi.zero_apply],
    Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Pi.single_apply, Ne.symm hc]
  · simp

theorem blockSphere_logMean_bound (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) {n : ℕ}
    (hn : 0 < n) : ∀ (B : ℕ) (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
      (u : BlockSphere B n), IsMultiHomogeneous a g → eval (blockPoint u) g ≠ 0 →
      Real.log ‖eval (blockPoint u) g‖ - (∑ b, (a b : ℝ)) / 2 * (harmonic (n - 1) : ℝ) ≤
        blockSphereMean B n g := by
  haveI hP1 : IsProbabilityMeasure (sphereProb n) := sphereMeasure_isProbability hn
  intro B
  induction B with
  | zero =>
    intro a g u _ _
    have hm : Measurable fun z : BlockSphere 0 n => Real.log ‖eval (blockPoint z) g‖ :=
      (measurable_eval_blockCoords g).norm.log
    unfold blockSphereMean blockSphereProb
    rw [Measure.pi_of_empty _ u, integral_dirac' _ _ hm.stronglyMeasurable]
    simp
  | succ B ih =>
    intro a g u hg hu
    haveI hP2 : IsProbabilityMeasure (blockSphereProb B n) := by
      unfold blockSphereProb; infer_instance
    have hu_split : (lh0Split B n).symm (u 0, fun b => u b.succ) = u := blockSplitEquiv_self u
    have hg0 : g ≠ 0 := by rintro rfl; exact hu (by simp)
    have hIpi := hInt (B + 1) n a g hg0 hg
    have hmp : MeasurePreserving (lh0Split B n) (blockSphereProb (B + 1) n)
        ((sphereProb n).prod (blockSphereProb B n)) :=
      measurePreserving_piFinSuccAbove (fun _ => sphereProb n) 0
    have hmp' := hmp.symm (lh0Split B n)
    have hIprod : Integrable (fun p => Real.log ‖eval (blockPoint ((lh0Split B n).symm p)) g‖)
        ((sphereProb n).prod (blockSphereProb B n)) :=
      (hmp'.integrable_comp_emb (lh0Split B n).symm.measurableEmbedding).mpr hIpi
    have hmean : blockSphereMean (B + 1) n g = ∫ y, ∫ x,
        Real.log ‖eval (blockPoint ((lh0Split B n).symm (x, y))) g‖ ∂sphereProb n
          ∂blockSphereProb B n := by
      unfold blockSphereMean
      rw [← hmp'.integral_comp (lh0Split B n).symm.measurableEmbedding
        (fun z => Real.log ‖eval (blockPoint z) g‖), integral_prod_symm _ hIprod]
    have hfirst : ∀ x y, eval (spherePoint x) (aeval (lh0First y) g) =
        eval (blockPoint ((lh0Split B n).symm (x, y))) g := by
      intro x y; rw [eval_aeval_alt, firstBlockSubst_eval]
    have hrest : ∀ y, eval (blockPoint y) (aeval (lh0Rest (spherePoint (u 0))) g) =
        eval (blockPoint ((lh0Split B n).symm (u 0, y))) g := by
      intro y; rw [eval_aeval_alt, restBlockSubst_eval]
    have hmh := restBlockSubst_isMultiHomogeneous hg (spherePoint (u 0))
    have hhu : eval (blockPoint fun b => u b.succ) (aeval (lh0Rest (spherePoint (u 0))) g) ≠ 0 := by
      rw [hrest, hu_split]; exact hu
    have hIB := ih (fun b => a b.succ) _ _ hmh hhu
    have hnull := null_of_logBound hn hInt ih (fun b => a b.succ) _ _ hmh hhu
    have hae : ∀ᵐ y ∂blockSphereProb B n,
        eval (blockPoint ((lh0Split B n).symm (u 0, y))) g ≠ 0 := by
      have hset : {y | ¬ eval (blockPoint ((lh0Split B n).symm (u 0, y))) g ≠ 0} =
          {z | eval (blockPoint z) (aeval (lh0Rest (spherePoint (u 0))) g) = 0} := by
        ext y
        simp only [Set.mem_setOf_eq, not_not, hrest]
      rw [ae_iff, hset]
      exact hnull
    have hh0 : aeval (lh0Rest (spherePoint (u 0))) g ≠ 0 := by
      intro h0; apply hhu; rw [h0]; simp
    have hIh := hInt B n _ _ hh0 hmh
    have hSJy : ∀ y, eval (blockPoint ((lh0Split B n).symm (u 0, y))) g ≠ 0 →
        Real.log ‖eval (blockPoint ((lh0Split B n).symm (u 0, y))) g‖ -
            (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
          ∫ x, Real.log ‖eval (blockPoint ((lh0Split B n).symm (x, y))) g‖ ∂sphereProb n := by
      intro y hy
      have hnorm : ‖((u 0 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))‖ = 1 := by
        simpa using (u 0).2
      have h := (hSJ n (a 0) (aeval (lh0First y) g) ((u 0 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))
        (firstBlockSubst_isHomogeneous hg y) hnorm (by
          rw [show WithLp.ofLp ((u 0 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) =
            spherePoint (u 0) from rfl, hfirst]; exact hy)).2
      rw [show WithLp.ofLp ((u 0 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) =
        spherePoint (u 0) from rfl] at h
      simpa only [hfirst] using h
    have hstep : ∫ y, (Real.log ‖eval (blockPoint y) (aeval (lh0Rest (spherePoint (u 0))) g)‖ -
          (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ)) ∂blockSphereProb B n ≤
        ∫ y, ∫ x, Real.log ‖eval (blockPoint ((lh0Split B n).symm (x, y))) g‖ ∂sphereProb n
          ∂blockSphereProb B n := by
      refine integral_mono_ae (hIh.sub (integrable_const _)) hIprod.integral_prod_right ?_
      filter_upwards [hae] with y hy
      rw [hrest]
      exact hSJy y hy
    rw [integral_sub hIh (integrable_const _)] at hstep
    have hc : ∫ _y, (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ∂blockSphereProb B n =
        (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) := by simp
    rw [hc] at hstep
    rw [hmean, Fin.sum_univ_succ]
    have hIB' : Real.log ‖eval (blockPoint u) g‖ -
        (∑ b : Fin B, (a b.succ : ℝ)) / 2 * (harmonic (n - 1) : ℝ) ≤
        ∫ y, Real.log ‖eval (blockPoint y) (aeval (lh0Rest (spherePoint (u 0))) g)‖
          ∂blockSphereProb B n := by
      have := hIB
      rw [hrest, hu_split] at this
      exact this
    linarith

end ReciprocityTheory.MultiplicativeHeights
