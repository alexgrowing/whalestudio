import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private noncomputable def hI (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (InfinitePlace F → ℝ) ≃ₜ InfiniteAdeleRing F where
  toEquiv := (TR.infEq F).toEquiv
  continuous_toFun := TR.continuous_infEq F
  continuous_invFun := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem map_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ c : ENNReal, (infiniteAdeleMeasure F).map (hI F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := by
  have hH : ((infiniteAdeleMeasure F).map (hI F).symm).IsAddHaarMeasure :=
    (TR.infEq F).symm.toAddEquiv.isAddHaarMeasure_map (infiniteAdeleMeasure F)
      (hI F).symm.continuous (hI F).continuous
  have h := Measure.isAddLeftInvariant_eq_smul ((infiniteAdeleMeasure F).map (hI F).symm)
    (volume : Measure (InfinitePlace F → ℝ))
  obtain ⟨c, hν⟩ : ∃ c : NNReal, (infiniteAdeleMeasure F).map (hI F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := ⟨_, h⟩
  refine ⟨(c : ENNReal), hν.trans ?_⟩
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

private theorem psi_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (y : InfinitePlace F → ℝ) :
    adelicChar F (infiniteAdeleInl (TR.infEq F y)) = Real.fourierChar (-∑ w, y w) := by
  rw [adelicChar_infiniteAdeleInl, ← Finset.sum_neg_distrib, addChar_map_finsetSum]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [infiniteAdelicChar_apply_of_isReal (IsTotallyReal.isReal w)]
  have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
      (TR.infEq F y w) = y w :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  rw [e2]

theorem UpperTheory.ConvolutionTheory.R2.C.splitA :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∃ (e : A F ≃ᵐ (InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F) (c : ENNReal), (∀ x, e x = (TR.pInf F x, x.2)) ∧
      (adeleMeasure F).map e = c • (volume : Measure (InfinitePlace F → ℝ)).prod (finiteAdeleMeasure F)) ∧
    ∀ x : A F, ψ x = (∏ w, Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F x w : ℝ) : ℂ))) * ((finiteAdelicChar F x.2 : Circle) : ℂ) := by
  intro F _ _ _
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨c, hc⟩ := map_inf F
    let e : A F ≃ᵐ (InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F :=
      MeasurableEquiv.prodCongr (hI F).symm.toMeasurableEquiv (MeasurableEquiv.refl _)
    refine ⟨e, c, fun x => rfl, ?_⟩
    have h1 : ((infiniteAdeleMeasure F).map (hI F).symm).prod
        ((finiteAdeleMeasure F).map id) =
        ((infiniteAdeleMeasure F).prod (finiteAdeleMeasure F)).map (Prod.map (hI F).symm id) :=
      Measure.map_prod_map _ _ (hI F).symm.measurable measurable_id
    rw [Measure.map_id, hc, Measure.prod_smul_left] at h1
    exact h1.symm
  · have hx : x = infiniteAdeleInl (TR.infEq F (TR.pInf F x)) + finiteAdeleInr x.2 := by
      have h0 : TR.infEq F (TR.pInf F x) = x.1 := (TR.infEq F).apply_symm_apply x.1
      rw [h0]
      exact (infiniteAdeleInl_add_finiteAdeleInr x).symm
    have h1 : ψ x = ((Real.fourierChar (-∑ w, TR.pInf F x w) : Circle) : ℂ) *
        ((finiteAdelicChar F x.2 : Circle) : ℂ) := by
      rw [ψ]
      conv_lhs => rw [hx]
      rw [AddChar.map_add_eq_mul, Circle.coe_mul, psi_inf, finiteAdelicChar_apply]
    rw [h1, Real.fourierChar_apply, ← Complex.exp_sum]
    congr 2
    push_cast
    rw [← Finset.mul_sum]
    ring_nf
