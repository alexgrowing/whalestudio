import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Qdist
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.GaussAbsMulOfMonomialOrder
import ReciprocityTheory.SemistableReduction.SemiDegCA
import Mathlib.NumberTheory.Height.NumberField

namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

theorem int_of_le_one (x : K) (h : ∀ w : FinitePlace K, w x ≤ 1) : ∃ y : 𝓞 K, (y : K) = x := by
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v.valuation K x ≤ 1 := by
    intro v
    have h1 := h (FinitePlace.mk v)
    first
      | (rw [FinitePlace.mk_apply, FinitePlace.norm_def] at h1
         have he : (1 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
           have h2 : Ideal.absNorm v.asIdeal ≠ 0 := by
             rw [Ne, Ideal.absNorm_eq_zero_iff]
             exact v.ne_bot
           have h3 : Ideal.absNorm v.asIdeal ≠ 1 := by
             rw [Ne, Ideal.absNorm_eq_one_iff]
             exact v.isPrime.ne_top
           have h4 : 1 < Ideal.absNorm v.asIdeal := by omega
           exact_mod_cast h4
         have h5 : Valued.v (FinitePlace.embedding v x) = v.valuation K x := by
           first
             | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
             | exact v.valuedAdicCompletion_eq_valuation' x
             | exact FinitePlace.valuation_embedding v x
             | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v x
             | rfl
         rw [h5] at h1
         exact (WithZeroMulInt.toNNReal_le_one_iff he).mp (by exact_mod_cast h1))
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x hv
  exact ⟨y, hy⟩

theorem finsum_log_eq {α : Type*} (f : α → ℝ) (hpos : ∀ a, 0 < f a)
    (hf : (Function.mulSupport f).Finite) : ∑ᶠ a, Real.log (f a) = Real.log (∏ᶠ a, f a) := by
  have h1 : Function.support (fun a => Real.log (f a)) ⊆ (hf.toFinset : Set α) := by
    intro a ha
    rw [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h
    exact (Function.mem_support.mp ha) (by rw [h, Real.log_one])
  have h2 : Function.mulSupport f ⊆ (hf.toFinset : Set α) := by
    rw [Set.Finite.coe_toFinset]
  rw [finsum_eq_sum_of_support_subset _ h1, finprod_eq_prod_of_mulSupport_subset _ h2]
  exact (Real.log_prod fun a _ => (hpos a).ne').symm

private lemma gaussAbs_of_lemma {κ : Type*} (F : MvPolynomial κ K) (hF : F ≠ 0) (w : FinitePlace K)
    (hw : ∀ s ∈ F.support, w (F.coeff s) = 1) : ReciprocityTheory.MultiplicativeHeights.gaussAbs w F = 1 := by
  have hle : (F.support.sup fun s => (w (F.coeff s)).toNNReal) ≤ 1 :=
    Finset.sup_le fun s hs => by rw [hw s hs]; simp
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hF
  have hs' : s ∈ F.support := MvPolynomial.mem_support_iff.mpr hs
  have hge : (1 : NNReal) ≤ F.support.sup fun s => (w (F.coeff s)).toNNReal := by
    have h1 := Finset.le_sup (f := fun s => (w (F.coeff s)).toNNReal) hs'
    rw [hw s hs'] at h1
    simpa using h1
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  rw [le_antisymm hle hge]
  simp

private lemma gaussAbs_cover_lemma_2 {κ : Type*} (F : MvPolynomial κ K) (hF : F ≠ 0) :
    (⋃ s ∈ (F.support : Set (κ →₀ ℕ)), Function.mulSupport fun w : FinitePlace K => w (F.coeff s)).Finite ∧
    ∀ w : FinitePlace K, w ∉ (⋃ s ∈ (F.support : Set (κ →₀ ℕ)),
      Function.mulSupport fun w : FinitePlace K => w (F.coeff s)) → ReciprocityTheory.MultiplicativeHeights.gaussAbs w F = 1 := by
  refine ⟨Set.Finite.biUnion F.support.finite_toSet fun s hs =>
    FinitePlace.mulSupport_finite (MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hs)), ?_⟩
  intro w hw
  apply gaussAbs_of_lemma F hF w
  intro s hs
  by_contra hne
  exact hw (Set.mem_biUnion (Finset.mem_coe.mpr hs) (Function.mem_mulSupport.mpr hne))

theorem gaussAbs_support_finite {κ : Type*} (F : MvPolynomial κ K) :
    (Function.support fun w : FinitePlace K => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w F)).Finite := by
  by_cases hF : F = 0
  · subst hF
    simp [ReciprocityTheory.MultiplicativeHeights.gaussAbs]
  · obtain ⟨hfin, hone⟩ := gaussAbs_cover_lemma_2 F hF
    refine hfin.subset ?_
    intro w hw
    by_contra hne
    exact (Function.mem_support.mp hw) (by rw [hone w hne, Real.log_one])

theorem gaussAbs_C_mul {κ : Type} [Fintype κ] (w : FinitePlace K) (c : K) (F : MvPolynomial κ K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C c * F) = w c * ReciprocityTheory.MultiplicativeHeights.gaussAbs w F := by
  by_cases hc : c = 0
  · subst hc
    simp [ReciprocityTheory.MultiplicativeHeights.gaussAbs]
  · have hw : 0 < w c := by
      first
        | exact w.pos_iff.mpr hc
        | exact (FinitePlace.pos_iff).mpr hc
    have hsupp : (MvPolynomial.C c * F).support = F.support := by
      rw [MvPolynomial.C_mul', MvPolynomial.support_smul_eq hc]
    unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
    rw [hsupp]
    simp_rw [MvPolynomial.coeff_C_mul, map_mul, Real.toNNReal_mul hw.le]
    rw [← NNReal.mul_finset_sup, NNReal.coe_mul, Real.coe_toNNReal _ hw.le]

theorem torusMean_C_mul {κ : Type} [Fintype κ] (z : ℂ) (hz : z ≠ 0) (f : MvPolynomial κ ℂ)
    (hf : f ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.C z * f) = Real.log ‖z‖ + ReciprocityTheory.MultiplicativeHeights.torusMean f := by
  have hb := ReciprocityTheory.MultiplicativeHeights.Closed.torusMeanBasic κ
  rw [hb.2.1 _ _ (by simpa using hz) hf, ← MvPolynomial.monomial_zero', hb.2.2]

end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

theorem gaussAbs_mulSupport_finite {κ : Type*} (F : MvPolynomial κ K) (hF : F ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K => ReciprocityTheory.MultiplicativeHeights.gaussAbs w F).Finite := by
  obtain ⟨hfin, hone⟩ := gaussAbs_cover_lemma_2 F hF
  refine hfin.subset ?_
  intro w hw
  by_contra hne
  exact (Function.mem_mulSupport.mp hw) (hone w hne)

theorem finsum_log_norm (c : K) (hc : c ≠ 0) :
    ∑ᶠ w : FinitePlace K, Real.log (w c) = -Real.log |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
  have hpos : ∀ w : FinitePlace K, 0 < w c := by
    intro w
    first
      | exact w.pos_iff.mpr hc
      | exact (FinitePlace.pos_iff).mpr hc
      | exact lt_of_le_of_ne (by positivity) (fun h => hc (by simpa using h.symm))
  rw [finsum_log_eq (fun w : FinitePlace K => w c) hpos (FinitePlace.mulSupport_finite hc),
    FinitePlace.prod_eq_inv_abs_norm hc]
  first
    | (rw [Rat.cast_inv, Rat.cast_abs, Real.log_inv])
    | (push_cast; rw [Real.log_inv])
    | simp [Real.log_inv]

theorem hT_C_mul {κ : Type} [Fintype κ] (F : MvPolynomial κ K) (hF : F ≠ 0) (c : K) (hc : c ≠ 0) :
    hT (MvPolynomial.C c * F) = hT F := by
  unfold hT
  congr 1
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C c * F)) =
      ∑ᶠ w : FinitePlace K, Real.log (w c) +
        ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w F) := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun w => ?_
      rw [gaussAbs_C_mul, Real.log_mul (FinitePlace.pos_iff.mpr hc).ne'
        (ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w F hF).ne']
    · refine (FinitePlace.hasFiniteMulSupport hc).subset ?_
      intro w hw h1
      apply hw
      simp only at h1 ⊢
      rw [h1, Real.log_one]
    · exact gaussAbs_support_finite F
  have harch : ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ (MvPolynomial.C c * F)) =
      ∑ σ : K →+* ℂ, Real.log ‖σ c‖ + ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ F) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, MvPolynomial.map_C]
    refine torusMean_C_mul _ ((map_ne_zero σ).mpr hc) _ ?_
    intro h0
    apply hF
    exact MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero])
  rw [hfin, harch, finsum_log_norm c hc, ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq c hc]
  ring

end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

noncomputable def contId {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) : Ideal (𝓞 K) :=
  Ideal.span (Set.range fun s : G₀.support => G₀.coeff s)

theorem contId_ne_bot {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) : contId G₀ ≠ ⊥ := by
  intro hb
  rw [contId, Ideal.span_eq_bot] at hb
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp h
  exact hs (hb _ ⟨⟨s, MvPolynomial.mem_support_iff.mpr hs⟩, rfl⟩)

private lemma place_nonneg_lemma_3 (w : FinitePlace K) (x : K) : 0 ≤ w x := by
  first
    | positivity
    | exact AbsoluteValue.nonneg _ _
    | exact w.1.nonneg _
    | exact norm_nonneg _
    | simp

theorem gaussAbs_eq_iSup {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) (w : FinitePlace K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) =
      ⨆ i : G₀.support, w ((G₀.coeff i : 𝓞 K) : K) := by
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := by
    first
      | exact RingOfIntegers.coe_injective
      | exact IsFractionRing.injective (𝓞 K) K
      | exact FaithfulSMul.algebraMap_injective (𝓞 K) K
  obtain ⟨s0, hs0⟩ := MvPolynomial.ne_zero_iff.mp h
  have hs0' : s0 ∈ G₀.support := MvPolynomial.mem_support_iff.mpr hs0
  have hbdd : BddAbove (Set.range fun i : G₀.support => w ((G₀.coeff i : 𝓞 K) : K)) :=
    (Set.finite_range _).bddAbove
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  rw [MvPolynomial.support_map_of_injective _ hinj]
  simp_rw [MvPolynomial.coeff_map]
  apply le_antisymm
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup G₀.support ⟨s0, hs0'⟩
      (fun s => (w (algebraMap (𝓞 K) K (G₀.coeff s))).toNNReal)
    rw [heq, Real.coe_toNNReal _ (place_nonneg_lemma_3 w _)]
    exact le_ciSup hbdd ⟨i, hi⟩
  · haveI : Nonempty G₀.support := ⟨⟨s0, hs0'⟩⟩
    apply ciSup_le
    rintro ⟨i, hi⟩
    have hle := Finset.le_sup (f := fun s => (w (algebraMap (𝓞 K) K (G₀.coeff s))).toNNReal) hi
    calc w ((G₀.coeff i : 𝓞 K) : K) = ((w (algebraMap (𝓞 K) K (G₀.coeff i))).toNNReal : ℝ) :=
          (Real.coe_toNNReal _ (place_nonneg_lemma_3 w _)).symm
      _ ≤ _ := NNReal.coe_le_coe.mpr hle

theorem absNorm_mul_gauss {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) :
    (Ideal.absNorm (contId G₀) : ℝ) *
      ∏ᶠ w : FinitePlace K, ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) = 1 := by
  have hx : (fun s : G₀.support => G₀.coeff s) ≠ 0 := by
    obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr h
    intro h0
    exact MvPolynomial.mem_support_iff.mp hs (congrFun h0 ⟨s, hs⟩)
  have := NumberField.absNorm_mul_finprod_finitePlace_eq_one hx
  rw [finprod_congr (gaussAbs_eq_iSup G₀ h)]
  exact this

theorem mem_inv_of {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) (x : K)
    (hx : ∀ s, ∃ y : 𝓞 K, (y : K) = x * ((G₀.coeff s : 𝓞 K) : K)) :
    x ∈ ((contId G₀ : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := by
  have hI : ((contId G₀ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (contId_ne_bot G₀ h)
  rw [FractionalIdeal.mem_inv_iff hI]
  intro y hy
  have hy2 : ∃ y', y' ∈ contId G₀ ∧ algebraMap (𝓞 K) K y' = y := by
    first
      | exact (FractionalIdeal.mem_coeIdeal _).mp hy
      | exact FractionalIdeal.mem_coeIdeal.mp hy
  obtain ⟨y', hy', rfl⟩ := hy2
  rw [FractionalIdeal.mem_one_iff]
  have key : ∃ z : 𝓞 K, (z : K) = x * (y' : K) := by
    clear hy
    unfold contId at hy'
    induction hy' using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨⟨s, _⟩, rfl⟩ := ha
      exact hx s
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨z1, h1⟩ := ha
      obtain ⟨z2, h2⟩ := hb
      refine ⟨z1 + z2, ?_⟩
      first
        | (push_cast; linear_combination h1 + h2)
        | (simp only [map_add]; linear_combination h1 + h2)
        | (simp; linear_combination h1 + h2)
    | smul r a _ ha =>
      obtain ⟨z, hz⟩ := ha
      refine ⟨r * z, ?_⟩
      rw [smul_eq_mul]
      first
        | (push_cast; linear_combination (r : K) * hz)
        | (simp only [map_mul]; linear_combination (algebraMap (𝓞 K) K r) * hz)
        | (simp; linear_combination (r : K) * hz)
  obtain ⟨z, hz⟩ := key
  first
    | exact ⟨z, hz⟩
    | exact ⟨z, by simpa using hz⟩

theorem relIndex_inv {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) :
    (((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex
      (((contId G₀ : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).toAddSubgroup : ℕ) : ℚ) = Ideal.absNorm (contId G₀) := by
  set J : FractionalIdeal (𝓞 K)⁰ K := ↑(contId G₀) with hJdef
  have hJ : J ≠ 0 := by
    rw [hJdef, Ne, FractionalIdeal.coeIdeal_eq_zero]; exact contId_ne_bot G₀ h
  have hfg : ((J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).FG :=
    FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have h1 : (1 : Submodule (𝓞 K) K) ≤ ((J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    have h2 := FractionalIdeal.inv_anti_mono hJ one_ne_zero FractionalIdeal.coeIdeal_le_one
    rw [inv_one] at h2
    have h3 : ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤
        ((J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := h2
    rwa [FractionalIdeal.coe_one] at h3
  have key := ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one _ hfg h1
  have he : (⟨((J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (𝓞 K)⁰ K) = J⁻¹ := rfl
  have hN : (Ideal.absNorm (contId G₀) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact contId_ne_bot G₀ h
  rw [he, map_inv₀, show FractionalIdeal.absNorm J = Ideal.absNorm (contId G₀) from
    FractionalIdeal.coeIdeal_absNorm _, inv_mul_eq_one₀ hN] at key
  exact key.symm

end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
