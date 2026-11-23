import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal Pointwise

private theorem inv_map_sub {G P : Type} [Group G] [Group P] [MeasurableSpace G] [MeasurableSpace P]
    [MeasurableInv G] [MeasurableInv P] (μ : Measure G) [μ.IsInvInvariant] (U : Subgroup G)
    (f : G →* P) (hf : Measurable f) (hU : MeasurableSet (U : Set G)) (E : Set P) (hE : MeasurableSet E) :
    ((μ.restrict (U : Set G)).map f) E⁻¹ = ((μ.restrict (U : Set G)).map f) E := by
  rw [Measure.map_apply hf hE.inv, Measure.map_apply hf hE, Measure.restrict_apply (hf hE.inv),
    Measure.restrict_apply (hf hE)]
  have h : f ⁻¹' E⁻¹ ∩ (U : Set G) = (f ⁻¹' E ∩ (U : Set G))⁻¹ := by
    ext x
    simp [Set.mem_inv, map_inv, Subgroup.inv_mem_iff]
  rw [h, Measure.measure_inv]

private theorem inv_all {P : Type} [Group P] [MeasurableSpace P] [MeasurableInv P] (ν : Measure P)
    (h : ∀ E, MeasurableSet E → ν E⁻¹ = ν E) (E : Set P) : ν E⁻¹ = ν E := by
  have hi : ν.inv = ν := Measure.ext fun E hE => by rw [Measure.inv_apply]; exact h E hE
  rw [← Measure.inv_apply, hi]

theorem UpperTheory.local_unimodular_of_exists_haar_measure :
    HaarEx → UniLoc := by
  intro hH V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hRP μ μi m hμ hμi hm
  haveI := hμ.1
  haveI := hμ.2
  haveI := hμi
  haveI := fun v => hm v
  have key : ∀ (S : Finset V) (A : Set Gi) (B : ∀ v : S, Set (Gv v)),
      μi A⁻¹ * ∏ v : S, m v (B v)⁻¹ = μi A * ∏ v : S, m v (B v) := by
    intro S A B
    obtain ⟨a, ha, hE⟩ := hH V G Gi Gv q p K hRP μ μi m hμ.1 hμi hm S
    have hE' : (μ.restrict (US p K S : Set G)).map (prS q p S) = a • μi.prod (Measure.pi fun v : S => m v) := hE
    have hf : Measurable (prS q p S) := by
      have h1 : Measurable q := hRP.cq.measurable
      have h2 : Measurable fun g : G => fun v : S => p v g :=
        measurable_pi_lambda _ fun v => (hRP.cp v).measurable
      exact h1.prodMk h2
    have hU : MeasurableSet (US p K S : Set G) := (hRP.opnU S).measurableSet
    have h1 := inv_all ((μ.restrict (US p K S : Set G)).map (prS q p S))
      (inv_map_sub μ (US p K S) (prS q p S) hf hU) (A ×ˢ Set.pi Set.univ B)
    have hset : (A ×ˢ Set.pi Set.univ B)⁻¹ = A⁻¹ ×ˢ Set.pi Set.univ (fun v => (B v)⁻¹) := by
      ext ⟨x, y⟩
      simp [Set.mem_prod, Set.mem_pi, Set.mem_inv]
    rw [hE', hset, Measure.smul_apply, Measure.smul_apply, Measure.prod_prod, Measure.prod_prod,
      Measure.pi_pi, Measure.pi_pi, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul] at h1
    exact (ENNReal.mul_right_inj (by exact_mod_cast ha) ENNReal.coe_ne_top).1 h1
  have hinv : ∀ A : Set Gi, μi A⁻¹ = μi A := by
    intro A
    have h := key ∅ A (fun _ => Set.univ)
    simpa using h
  refine ⟨⟨hμi, ⟨Measure.ext fun A _ => by rw [Measure.inv_apply]; exact hinv A⟩⟩, fun v => ⟨hm v, ⟨Measure.ext fun B _ => ?_⟩⟩⟩
  rw [Measure.inv_apply]
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : Gi)
  have hpos : μi C ≠ 0 := (Measure.measure_pos_of_mem_nhds μi hC1).ne'
  have htop : μi C ≠ ⊤ := hC.measure_lt_top.ne
  let v0 : ({v} : Finset V) := ⟨v, Finset.mem_singleton_self v⟩
  have h := key {v} C (Function.update (fun _ => Set.univ) v0 B)
  rw [hinv C, Fintype.prod_subsingleton _ v0, Fintype.prod_subsingleton _ v0] at h
  simp only [Function.update_self] at h
  exact (ENNReal.mul_right_inj hpos htop).1 h
