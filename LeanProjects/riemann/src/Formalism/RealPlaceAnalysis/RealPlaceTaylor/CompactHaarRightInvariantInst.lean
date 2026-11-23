import Formalism.RealPlaceAnalysis.SmoothOnGVIff

open Matrix MeasureTheory MeasureTheory.Measure

noncomputable section

namespace Formalism.REAL

section P0KLinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma continuous_exp_real_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  exact NormedSpace.exp_continuous.comp (by fun_prop)

end P0KLinfty

lemma toM_injective' {n : ℕ} {ε : Fin n → Bool} {g h : UJ ε} (hgh : toM g = toM h) : g = h := by
  exact Subtype.ext (Units.ext hgh)

theorem group_exponential_facts : ExpGFacts := by
  intro n ε X hX
  have hE : ∀ t : ℝ, toM (expG ε X t) = NormedSpace.exp ((t : ℂ) • X) := fun t => toM_expG ε X t hX
  have hcont : Continuous (fun t : ℝ => expG ε X t) := by
    have hcU : Continuous (fun t : ℝ => ((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
      rw [Units.continuous_iff]
      refine ⟨?_, ?_⟩
      · have h1 : (Units.val ∘ fun t : ℝ => ((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) =
            fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := funext hE
        rw [h1]
        exact continuous_exp_real_smul X
      · have h2 : (fun t : ℝ => ((((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ :
            (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
            fun t : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • X) := by
          funext t
          apply Units.inv_eq_of_mul_eq_one_right
          show toM (expG ε X t) * _ = 1
          rw [hE, ← Matrix.exp_add_of_commute _ _
            (((Commute.refl X).smul_left ((t : ℝ) : ℂ)).smul_right (((-t : ℝ)) : ℂ)), ← add_smul]
          push_cast
          rw [add_neg_cancel, zero_smul, NormedSpace.exp_zero]
        rw [h2]
        exact (continuous_exp_real_smul X).comp continuous_neg
    exact continuous_induced_rng.2 hcU
  refine ⟨?_, ?_, hcont, ?_⟩
  · apply toM_injective'
    rw [hE]
    simp
    rfl
  · intro s t
    apply toM_injective'
    show toM (expG ε X (s + t)) = toM (expG ε X s) * toM (expG ε X t)
    rw [hE, hE, hE, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl X).smul_left ((s : ℝ) : ℂ)).smul_right ((t : ℝ) : ℂ))]
    congr 1
    push_cast
    rw [add_smul]
  · intro hK
    have hk : ∀ t : ℝ, ((expK ε X t : KG ε) : UJ ε) = expG ε X t := by
      intro t
      unfold expK
      rw [dif_pos hK]
    refine ⟨hk, ?_⟩
    apply continuous_induced_rng.2
    have h3 : (Subtype.val ∘ fun t : ℝ => expK ε X t) = fun t : ℝ => expG ε X t := funext hk
    rw [h3]
    exact hcont

lemma compact_haar_probability (n : ℕ) (ε : Fin n → Bool) : IsProbabilityMeasure (muK ε) := by
  unfold muK
  constructor
  have h := MeasureTheory.Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KG ε)))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

instance compact_haar_probability_inst (n : ℕ) (ε : Fin n → Bool) : IsProbabilityMeasure (muK ε) := compact_haar_probability n ε

lemma compact_haar_unique_left {n : ℕ} {ε : Fin n → Bool} (ν : Measure (KG ε)) [IsMulLeftInvariant ν]
    [IsProbabilityMeasure ν] : ν = muK ε := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    TopologicalSpace.secondCountableTopology_induced _ _ MulOpposite.unop
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    TopologicalSpace.secondCountableTopology_induced _ _ (Units.embedProduct _)
  haveI : SecondCountableTopology (UJ ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ)
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  have h := MeasureTheory.Measure.haarMeasure_unique ν (⊤ : TopologicalSpace.PositiveCompacts (KG ε))
  rw [h, TopologicalSpace.PositiveCompacts.coe_top, measure_univ, one_smul]
  rfl

lemma compact_haar_right_invariant (n : ℕ) (ε : Fin n → Bool) (k : KG ε) :
    Measure.map (fun x => x * k) (muK ε) = muK ε := by
  haveI : IsMulLeftInvariant (muK ε) := by
    unfold muK
    infer_instance
  have hm : Measurable (fun x : KG ε => x * k) := measurable_mul_const k
  haveI : IsProbabilityMeasure (Measure.map (fun x => x * k) (muK ε)) :=
    isProbabilityMeasure_map hm.aemeasurable
  haveI : IsMulLeftInvariant (Measure.map (fun x => x * k) (muK ε)) := by
    constructor
    intro g
    rw [Measure.map_map (measurable_const_mul g) hm]
    have e : ((g * ·) ∘ (· * k)) = ((· * k) ∘ (g * ·) : KG ε → KG ε) := by
      funext x
      simp [mul_assoc]
    rw [e, ← Measure.map_map hm (measurable_const_mul g), map_mul_left_eq_self]
  exact compact_haar_unique_left _

instance compact_haar_right_invariant_inst (n : ℕ) (ε : Fin n → Bool) : IsMulRightInvariant (muK ε) :=
  ⟨fun k => compact_haar_right_invariant n ε k⟩

theorem compact_haar_holds : KHaar := by
  intro n ε
  haveI : IsMulLeftInvariant (muK ε) := by
    unfold muK
    infer_instance
  refine ⟨compact_haar_probability n ε, fun k => map_mul_left_eq_self _ k, fun k => compact_haar_right_invariant n ε k, ?_⟩
  haveI : IsProbabilityMeasure (Measure.map (fun x : KG ε => x⁻¹) (muK ε)) :=
    isProbabilityMeasure_map measurable_inv.aemeasurable
  haveI : IsMulLeftInvariant (Measure.map (fun x : KG ε => x⁻¹) (muK ε)) := by
    constructor
    intro g
    rw [Measure.map_map (measurable_const_mul g) measurable_inv]
    have e : ((g * ·) ∘ (fun x : KG ε => x⁻¹)) = ((fun x : KG ε => x⁻¹) ∘ (· * g⁻¹)) := by
      funext x
      simp
    rw [e, ← Measure.map_map measurable_inv (measurable_mul_const g⁻¹), compact_haar_right_invariant]
  exact compact_haar_unique_left _

theorem compact_integration_by_parts : KByParts := by
  intro n ε E _ _ _ F D Z hZ hF hD hder
  haveI : IsMulRightInvariant (muK ε) := ⟨fun g => compact_haar_right_invariant n ε g⟩
  haveI : IsProbabilityMeasure (muK ε) := compact_haar_probability n ε
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    TopologicalSpace.secondCountableTopology_induced _ _ MulOpposite.unop
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    TopologicalSpace.secondCountableTopology_induced _ _ (Units.embedProduct _)
  haveI : SecondCountableTopology (UJ ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ)
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  obtain ⟨h0, hadd, -, hKf⟩ := group_exponential_facts n ε Z hZ.1
  obtain ⟨hk, -⟩ := hKf hZ
  have hhom : ∀ s t : ℝ, expK ε Z (s + t) = expK ε Z s * expK ε Z t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hk, hk, hk, hadd]
  have hzero : expK ε Z 0 = 1 := by
    apply Subtype.ext
    exact (hk 0).trans h0
  have hderiv : ∀ (k : KG ε) (t : ℝ),
      HasDerivAt (fun s => F (k * expK ε Z s)) (D (k * expK ε Z t)) t := by
    intro k t
    have h := hder (k * expK ε Z t)
    rw [← sub_self t] at h
    have e : (fun s => F (k * expK ε Z s)) = fun s => F (k * expK ε Z t * expK ε Z (s - t)) := by
      funext s
      rw [mul_assoc, ← hhom, add_sub_cancel]
    rw [e]
    exact h.comp_sub_const t t
  obtain ⟨C, hC⟩ : ∃ C, ∀ y : KG ε, ‖D y‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hD.norm).bddAbove
    exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩
  obtain ⟨CF, hCF⟩ : ∃ C, ∀ y : KG ε, ‖F y‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hF.norm).bddAbove
    exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩
  have hcomp : ∀ t : ℝ, Continuous (fun k : KG ε => k * expK ε Z t) := fun t =>
    continuous_id.mul continuous_const
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (x₀ := (0 : ℝ))
    (F := fun t k => F (k * expK ε Z t)) (F' := fun t k => D (k * expK ε Z t))
    (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hF.comp (hcomp t)).aestronglyMeasurable)
    (Integrable.mono' (integrable_const CF) (hF.comp (hcomp 0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => hCF _))
    (hD.comp (hcomp 0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k t _ => hC _)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ => hderiv k t)
  have hconst : (fun t : ℝ => ∫ k, F (k * expK ε Z t) ∂(muK ε)) = fun _ => ∫ k, F k ∂(muK ε) := by
    funext t
    exact integral_mul_right_eq_self F (expK ε Z t)
  have h2 : HasDerivAt (fun _ : ℝ => ∫ k, F k ∂(muK ε)) (∫ k, D (k * expK ε Z 0) ∂(muK ε)) 0 := by
    rw [← hconst]
    exact key.2
  have h3 := h2.unique (hasDerivAt_const (0 : ℝ) (∫ k, F k ∂(muK ε)))
  simp only [hzero, mul_one] at h3
  exact h3

end Formalism.REAL
