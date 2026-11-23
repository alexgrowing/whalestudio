import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem absHalf_eq_sqrt {E : Type} [Field E] [NumberField E] [IsCMField E] (u : HeightOneSpectrum (𝓞 E))
    (x : u.adicCompletion E) (hx : x ≠ 0) : absHalf u x = ((Real.sqrt ‖x‖ : ℝ) : ℂ) := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold absHalf
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, Formalism.UG.ordL, dif_neg hv, neg_neg]
  simp [Formalism.UG.qV]

theorem UpperTheory.ConvolutionTheory.G2.absProd :
    UpperTheory.ConvolutionTheory.G2.AbsProd := by
  intro E _ _ _ R hR
  have hne : ∀ u : HeightOneSpectrum (𝓞 E), algebraMap E (u.adicCompletion E) R ≠ 0 := fun u =>
    (_root_.map_ne_zero _).2 hR
  have hfun : (fun u : Pl E => absHalf u (algebraMap E (u.adicCompletion E) R)) =
      fun u : Pl E => ((Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖ : ℝ) : ℂ) :=
    funext fun u => absHalf_eq_sqrt u _ (hne u)
  have hmult : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  have hPF := prod_abs_eq_one hR
  simp only [hmult] at hPF
  have hfp : ∏ᶠ w : FinitePlace E, w R =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) R‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
    rfl
  rw [hfp] at hPF
  have hgfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
      ‖algebraMap E (v.adicCompletion E) R‖).Finite := by
    refine ((FinitePlace.hasFiniteMulSupport hR).preimage
      (FinitePlace.equivHeightOneSpectrum (K := E)).symm.injective.injOn).subset fun v hv => ?_
    simp only [Set.mem_preimage, Function.mem_mulSupport, FinitePlace.equivHeightOneSpectrum_symm_apply] at hv ⊢
    exact hv
  have hsub : (Function.mulSupport fun u : Pl E =>
      ((Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖ : ℝ) : ℂ)) ⊆ (hgfin.toFinset : Set (Pl E)) := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    intro h1
    apply hu
    have h1' : ‖algebraMap E (u.adicCompletion E) R‖ = 1 := h1
    simp only [h1', Real.sqrt_one, Complex.ofReal_one]
  rw [hfun]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  rw [finprod_eq_prod _ hgfin] at hPF
  simp only [InfinitePlace.norm_embedding_eq]
  rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_eq_one]
  have hnn : 0 ≤ (∏ u ∈ hgfin.toFinset, Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖) *
      ∏ v : InfinitePlace E, v R :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) (Finset.prod_nonneg fun v _ => apply_nonneg v R)
  refine (pow_eq_one_iff_of_nonneg hnn two_ne_zero).1 ?_
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, mul_comm, ← hPF]
  congr 1
  exact Finset.prod_congr rfl fun u _ => Real.sq_sqrt (norm_nonneg _)
