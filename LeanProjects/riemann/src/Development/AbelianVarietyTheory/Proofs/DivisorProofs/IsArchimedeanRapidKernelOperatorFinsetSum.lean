import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem isOpenEmbedding_entriesGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_entriesGLInf.measurableEmbedding.measurable_comp_iff).1
    (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j)
  exact hF.measurable.comp h

theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

theorem IsRapidFInf.integrable {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin n) (Cinf E)} {η : X → Z →L[ℝ] ℝ} (h : IsRapidFInf ν k γ η)
    {W : GL (Fin n) (Cinf E) → ℂ} (hW : IsModGrowthInf W) (z : Z) (g : GL (Fin n) (Cinf E)) :
    Integrable (fun x => k x * (𝐞 (η x z) : ℂ) * W (g * γ x)) ν := by
  obtain ⟨hc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  refine ((h.2.2.2 N).const_mul (C * htInf g ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Measurable.aestronglyMeasurable ((h.1.mul ?_).mul ?_)
    · exact (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp (h.2.2.1 z)
    · exact measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop) h.2.1
  · rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    have h1 : htInf (g * γ x) ≤ htInf g * (htInf (γ x) * (1 + ‖η x‖)) :=
      (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (htInf_pos' _).le (by linarith [norm_nonneg (η x)])) (htInf_pos' _).le)
    have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
    rw [mul_pow] at h2
    calc ‖k x‖ * ‖W (g * γ x)‖ ≤ ‖k x‖ * (C * (htInf g ^ N * (htInf (γ x) * (1 + ‖η x‖)) ^ N)) :=
          mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
      _ = _ := by ring

theorem isKerOpInf_zero_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    IsKerOpInf (E := E) (n := n)
      (fun (_ : GL (Fin n) (Cinf E) → ℂ) (_ : Z) (_ : GL (Fin n) (Cinf E)) => (0 : ℂ)) := by
  refine ⟨Unit, inferInstance, 0, inferInstance, fun _ => 0, fun _ => 1, fun _ => 0, ?_, ?_⟩
  · exact ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_zero_measure⟩
  · intro W _ z g
    simp

theorem isKerOpInf_add_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T T' : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ} (hT : IsKerOpInf T) (hT' : IsKerOpInf T') :
    IsKerOpInf (fun W z g => T W z g + T' W z g) := by
  obtain ⟨X, mX, ν, hν, k, γ, η, hr, hT⟩ := hT
  obtain ⟨X', mX', ν', hν', k', γ', η', hr', hT'⟩ := hT'
  have e1 : MeasurableEmbedding (Sum.inl : X → X ⊕ X') :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => measurableSet_inl_image.2 hs⟩
  have e2 : MeasurableEmbedding (Sum.inr : X' → X ⊕ X') :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => measurableSet_inr_image.2 hs⟩
  refine ⟨X ⊕ X', inferInstance, ν.map Sum.inl + ν'.map Sum.inr, inferInstance, Sum.elim k k', Sum.elim γ γ',
    Sum.elim η η', ?_, ?_⟩
  · refine ⟨hr.1.sumElim hr'.1, fun i j => ?_, fun z => ?_, fun N => ?_⟩
    · have : (fun x : X ⊕ X' => ((Sum.elim γ γ' x : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
          Sum.elim (fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j)
            (fun x => (γ' x : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.1 i j).sumElim (hr'.2.1 i j)
    · have : (fun x : X ⊕ X' => Sum.elim η η' x z) = Sum.elim (fun x => η x z) (fun x => η' x z) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.2.1 z).sumElim (hr'.2.2.1 z)
    · rw [integrable_add_measure, e1.integrable_map_iff, e2.integrable_map_iff]
      exact ⟨hr.2.2.2 N, hr'.2.2.2 N⟩
  · intro W hW z g
    have i1 := hr.integrable hW z g
    have i2 := hr'.integrable hW z g
    show T W z g + T' W z g = _
    rw [integral_add_measure, e1.integral_map, e2.integral_map, hT W hW z g, hT' W hW z g]
    · rfl
    · rw [e1.integrable_map_iff]; exact i1
    · rw [e2.integrable_map_iff]; exact i2

theorem isKerOpInf_fintype_sum (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι]
    (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) (hT : ∀ i, IsKerOpInf (T i)) :
    IsKerOpInf (fun W z g => ∑ i, T i W z g) := by
  classical
  suffices h : ∀ s : Finset ι, IsKerOpInf (fun W z g => ∑ i ∈ s, T i W z g) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (isKerOpInf_zero_sum (E := E) (n := n) (Z := Z))
  | insert a s ha ih =>
    have : (fun W z g => ∑ i ∈ insert a s, T i W z g) = fun W z g => T a W z g + ∑ i ∈ s, T i W z g := by
      funext W z g; rw [Finset.sum_insert ha]
    rw [this]
    exact isKerOpInf_add_sum (hT a) ih

example : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι] (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ),
    (∀ i, IsKerOpInf (T i)) → IsKerOpInf (fun W z g => ∑ i, T i W z g) := isKerOpInf_fintype_sum

end GlobalTheory.JSW.MirCinf
