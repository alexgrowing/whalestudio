import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.IntegralConv

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem groupConv_sum_sum {G ι κ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (S : Finset ι) (T : Finset κ) (c : ι → ℂ) (d : κ → ℂ) (f : ι → G → ℂ) (g : κ → G → ℂ)
    (hf : ∀ i ∈ S, f i ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hg : ∀ j ∈ T, g j ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ (∑ i ∈ S, c i • f i) (∑ j ∈ T, d j • g j) =
      ∑ i ∈ S, ∑ j ∈ T, (c i * d j) • groupConv μ (f i) (g j) := by
  funext x
  have hint : ∀ i ∈ S, ∀ j ∈ T,
      Integrable (fun y => (c i * d j) * (f i y * g j (y⁻¹ * x))) μ := fun i hi j hj =>
    (integrable_mul_of_mem (hf i hi)
      ((hg j hj).1.continuous.comp (continuous_inv.mul continuous_const))).const_mul _
  have h1 : ∀ y, (∑ i ∈ S, c i • f i) y * (∑ j ∈ T, d j • g j) (y⁻¹ * x) =
      ∑ i ∈ S, ∑ j ∈ T, (c i * d j) * (f i y * g j (y⁻¹ * x)) := by
    intro y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [groupConv, h1]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => hint i hi j hj]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun j hj => hint i hi j hj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

theorem UpperTheory.ConvolutionTheory.H.thPMul :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (r s : LaurentRing n), Dom r → Dom s →
      Dom (r * s) ∧ thP μ r ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ ∧ BiI F (thP μ r) ∧ groupConv μ (thP μ r) (thP μ s) = thP μ (r * s) := by
  intro F _ _ _ _ n _ _ μ _ r s hr hs
  classical
  have hth : ∀ a : Fin n → ℤ, Antitone a →
      th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := fun a ha =>
    Submodule.smul_mem _ _ (dcoShape F n a ha).2.2.1
  refine ⟨fun a ha => ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, c, hc, rfl⟩ :=
      Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset r s ha)
    exact (hr b hb).add (hs c hc)
  · exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (hth a (hr a ha))
  · intro g y hy
    simp only [thP, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, th]
    constructor
    · exact Finset.sum_congr rfl fun a ha => by
        rw [((dcoShape F n a (hr a ha)).2.2.2 g y hy).1]
    · exact Finset.sum_congr rfl fun a ha => by
        rw [((dcoShape F n a (hr a ha)).2.2.2 g y hy).2]
  · have hz : ∀ a : Fin n → ℤ, (0 : ℂ) • th μ a = 0 := fun a => zero_smul _ _
    have ha : ∀ (a : Fin n → ℤ) (c d : ℂ), (c + d) • th μ a = c • th μ a + d • th μ a :=
      fun a c d => add_smul _ _ _
    have h1 : thP μ (r * s) = ∑ a ∈ r.coeff.support, ∑ b ∈ s.coeff.support,
        (r.coeff a * s.coeff b) • th μ (a + b) := by
      unfold thP
      rw [AddMonoidAlgebra.mul_def]
      simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single]
      rw [Finsupp.sum_sum_index hz ha]
      refine Finset.sum_congr rfl fun a _ => ?_
      beta_reduce
      rw [Finsupp.sum_sum_index hz ha]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact Finsupp.sum_single_index (hz _)
    rw [h1]
    unfold thP Finsupp.sum
    rw [groupConv_sum_sum μ _ _ _ _ _ _ (fun a ha => hth a (hr a ha)) (fun b hb => hth b (hs b hb))]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [thMul F n μ a b (hr a ha) (hs b hb)]
