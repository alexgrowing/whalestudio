import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.TateThesis.TracePairing
import GroundTheory.GlobalFields.TateThesis.ArchChars
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
import GroundTheory.GlobalFields.Adele.IdeleBasis
import GroundTheory.GlobalFields.Adele.Compact

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum NumberField.mixedEmbedding Topology Filter WithZero
open scoped NumberField.AdeleRing _root_.RestrictedProduct FourierTransform

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

variable (K) in

def mixedToInfinite : mixedSpace K →+ InfiniteAdeleRing K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toAddMonoidHom

omit [NumberField K] in
theorem homeomorphMixedSpace_mixedToInfinite (m : mixedSpace K) :
    homeomorphMixedSpace K (mixedToInfinite K m) = m := by
  rw [homeomorphMixedSpace_apply]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply m

omit [NumberField K] in
theorem mixedToInfinite_homeomorphMixedSpace (x : InfiniteAdeleRing K) :
    mixedToInfinite K (homeomorphMixedSpace K x) = x := by
  rw [homeomorphMixedSpace_apply]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply x

omit [NumberField K] in
theorem continuous_mixedToInfinite : Continuous (mixedToInfinite K) := by
  have : (mixedToInfinite K : mixedSpace K → InfiniteAdeleRing K) =
      (homeomorphMixedSpace K).symm := by
    funext m
    apply (homeomorphMixedSpace K).injective
    rw [homeomorphMixedSpace_mixedToInfinite, Homeomorph.apply_symm_apply]
  rw [this]
  exact (homeomorphMixedSpace K).symm.continuous

omit [NumberField K] in
theorem mixedToInfinite_mixedEmbedding (k : K) :
    mixedToInfinite K (mixedEmbedding K k) = algebraMap K (InfiniteAdeleRing K) k := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply _

omit [NumberField K] in
theorem mixedToInfinite_mul (m m' : mixedSpace K) :
    mixedToInfinite K (m * m') = mixedToInfinite K m * mixedToInfinite K m' :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm m m'

theorem mixedTrace_homeomorphMixedSpace (x : InfiniteAdeleRing K) :
    mixedTrace K (homeomorphMixedSpace K x) = infiniteTrace K x := by
  classical
  rw [mixedTrace_apply, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
    infiniteTrace_apply, ← Fintype.sum_subtype_add_sum_subtype (fun w => IsReal w)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [w.2.mult_eq_one, Nat.cast_one, one_mul, ← extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex.symm) _ _
      fun w => ?_
    have hw : IsComplex w.1 := w.2
    show 2 * (extensionEmbedding w.1 (x w.1)).re = (w.1.mult : ℝ) * _
    rw [hw.mult_eq_two, Nat.cast_ofNat]
    rfl

theorem exists_mixedSpace_char_eq (χ : AddChar (mixedSpace K) Circle) (hχ : Continuous χ)
    (h1 : ∀ a : 𝓞 K, χ (mixedEmbedding K (algebraMap (𝓞 K) K a)) = 1) :
    ∃ ξ : K, (∀ a : 𝓞 K,
        Algebra.trace ℚ K (ξ * algebraMap (𝓞 K) K a) ∈ (algebraMap ℤ ℚ).range) ∧
      ∀ m : mixedSpace K, χ m = 𝐞 (-mixedTrace K (mixedEmbedding K ξ * m)) := by
  classical
  set b := latticeBasis K
  set ω := integralBasis K
  have hbω : ∀ i, b i = mixedEmbedding K (ω i) := fun i => latticeBasis_apply K i
  have hω : ∀ i, ω i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i) := fun i =>
    integralBasis_apply K i

  have hline : ∀ i, ∃ τ : ℝ, ∀ t : ℝ, χ (t • b i) = Circle.exp (τ * t) := fun i =>
    (existsUnique_circleExp_of_continuous (fun t : ℝ => χ (t • b i))
      (hχ.comp (continuous_id.smul continuous_const))
      (fun s t => by rw [add_smul, AddChar.map_add_eq_mul])).exists
  choose τ hτ using hline
  have hn : ∀ i, ∃ n : ℤ, τ i = n * (2 * Real.pi) := fun i => by
    have h := hτ i 1
    rw [one_smul, mul_one, hbω, hω, h1] at h
    exact Circle.exp_eq_one.mp h.symm
  choose n hn using hn

  set ωd := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) ω
  set ξ : K := -∑ j, (n j : ℚ) • ωd j
  have hξω : ∀ i, Algebra.trace ℚ K (ξ * ω i) = -(n i : ℚ) := by
    intro i
    have : ∀ j, Algebra.trace ℚ K (ωd j * ω i) = if i = j then 1 else 0 := fun j => by
      rw [← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left _ _ _ _
    simp only [ξ, neg_mul, map_neg, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, this,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨ξ, fun a => ?_, fun m => ?_⟩
  · have ha : algebraMap (𝓞 K) K a = ∑ i, ((RingOfIntegers.basis K).repr a i : ℤ) • ω i := by
      conv_lhs => rw [← (RingOfIntegers.basis K).sum_repr a]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, hω]
    refine ⟨-∑ i, ((RingOfIntegers.basis K).repr a i : ℤ) * n i, ?_⟩
    rw [eq_intCast, ha, Finset.mul_sum, map_sum]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul, mul_left_comm, show ((((RingOfIntegers.basis K).repr a i : ℤ)) : K) =
      algebraMap ℚ K ((RingOfIntegers.basis K).repr a i : ℚ) by simp, ← Algebra.smul_def,
      map_smul, hξω, smul_eq_mul]
    ring
  · conv_lhs => rw [← b.sum_repr m]
    rw [addChar_map_finsetSum]
    have hT : mixedTrace K (mixedEmbedding K ξ * ∑ i, b.repr m i • b i) =
        -∑ i, b.repr m i * n i := by
      rw [Finset.mul_sum, map_sum]
      simp only [mul_smul_comm, map_smul, hbω, ← map_mul, mixedTrace_mixedEmbedding, hξω,
        smul_eq_mul, Rat.cast_neg, Rat.cast_intCast, mul_neg, Finset.sum_neg_distrib]
    conv_rhs => rw [← b.sum_repr m, hT, neg_neg, addChar_map_finsetSum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hτ, hn, Real.fourierChar_apply']
    congr 1
    ring

theorem exists_forall_valued_le_mem {v : HeightOneSpectrum (𝓞 K)} {W : Set (v.adicCompletion K)}
    (hW : W ∈ 𝓝 (0 : v.adicCompletion K)) :
    ∃ n : ℕ, ∀ y : v.adicCompletion K, Valued.v y ≤ exp (-(n : ℤ)) → y ∈ W := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hW
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := fun h ↦ γ.ne_zero
    (MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm))
  refine ⟨(-(log c)).toNat + 1, fun y hy ↦ hγ ?_⟩
  change Valued.v.restrict (y - 0) < γ.1
  rw [sub_zero, Valuation.restrict_lt_iff_lt_embedding, ← hc]
  refine hy.trans_lt (lt_of_lt_of_eq ?_ (exp_log hc0))
  rw [exp_lt_exp]
  omega

theorem valued_coe_algebraMap (v : HeightOneSpectrum (𝓞 K)) (d : 𝓞 K) :
    Valued.v ((algebraMap (𝓞 K) K d : K) : v.adicCompletion K) = v.intValuation d := by
  rw [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]

theorem exists_ne_zero_forall_intValuation_le (T : Finset (HeightOneSpectrum (𝓞 K)))
    (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ v ∈ T, v.intValuation d ≤ exp (-(n v : ℤ)) := by
  classical
  have hJ : (∏ v ∈ T, v.asIdeal ^ n v) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact ⟨d, hd0, fun v hv => (v.intValuation_le_pow_iff_mem d (n v)).mpr
    ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hd)⟩

theorem exists_forall_mul_mem_of_mem_nhds {W : Set (FiniteAdeleRing (𝓞 K) K)}
    (hW : W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ y ∈ integralFiniteAdeles (𝓞 K) K,
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K d) * y ∈ W := by
  classical
  obtain ⟨t, ⟨V, hVo, hVA, rfl⟩, h0, hsub⟩ :=
    (GroundTheory.Global.RestrictedProduct.isTopologicalBasis
      (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (fun v => Valued.isOpen_valuationSubring _)).mem_nhds_iff.mp hW
  have hT : {v | ¬ V v = (v.adicCompletionIntegers K : Set (v.adicCompletion K))}.Finite := hVA
  have hVn : ∀ v, V v ∈ 𝓝 (0 : v.adicCompletion K) := fun v => (hVo v).mem_nhds (h0 v)
  choose n hn using fun v => exists_forall_valued_le_mem (hVn v)
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_intValuation_le hT.toFinset n
  refine ⟨d, hd0, fun y hy => hsub fun v => ?_⟩
  show ((algebraMap (𝓞 K) K d : K) : v.adicCompletion K) * y v ∈ V v
  by_cases hv : v ∈ hT.toFinset
  · refine hn v _ ?_
    rw [Valuation.map_mul, valued_coe_algebraMap]
    exact (mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).mp (hy v))).trans
      (hd v hv)
  · have : V v = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by simpa using hv
    rw [this]
    exact mul_mem (coe_algebraMap_mem_adicCompletionIntegers v d) (hy v)

theorem exists_forall_finiteChar_mul_eq_one (χ : AddChar (FiniteAdeleRing (𝓞 K) K) Circle)
    (hχ : Continuous χ) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ y ∈ integralFiniteAdeles (𝓞 K) K,
      χ (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K d) * y) = 1 := by
  have hU : IsOpen {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} :=
    isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const))
      continuous_const
  have hW : χ ⁻¹' {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) :=
    (hU.preimage hχ).mem_nhds (by simp)
  obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun y hy => ?_⟩
  let H : Subgroup Circle :=
    { carrier := {z | ∃ y ∈ integralFiniteAdeles (𝓞 K) K,
        χ (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K d) * y) = z}
      one_mem' := ⟨0, zero_mem _, by rw [mul_zero, AddChar.map_zero_eq_one]⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, add_mem ha hb, by rw [mul_add, AddChar.map_add_eq_mul]⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, neg_mem ha, by rw [mul_neg, AddChar.map_neg_eq_inv]⟩ }
  have hH : H = ⊥ := GroundTheory.Global.Circle.subgroup_eq_bot_of_norm_sub_one_lt H
    (by rintro _ ⟨a, ha, rfl⟩; exact hd a ha)
  have hmem : χ (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K d) * y) ∈ H :=
    ⟨y, hy, rfl⟩
  rw [hH] at hmem
  exact Subgroup.mem_bot.mp hmem

@[simp] theorem adeleRing_mul_fst (x y : 𝔸[K]) : (x * y).1 = x.1 * y.1 := rfl

@[simp] theorem adeleRing_mul_snd (x y : 𝔸[K]) : (x * y).2 = x.2 * y.2 := rfl

theorem continuous_infiniteAdeleInl : Continuous (infiniteAdeleInl (K := K)) :=
  continuous_id.prodMk continuous_const

theorem continuous_finiteAdeleInr : Continuous (finiteAdeleInr (K := K)) :=
  continuous_const.prodMk continuous_id

theorem algebraMap_mul_infiniteAdeleInl (ξ : K) (z : InfiniteAdeleRing K) :
    algebraMap K 𝔸[K] ξ * infiniteAdeleInl z =
      infiniteAdeleInl (algebraMap K (InfiniteAdeleRing K) ξ * z) := by
  refine Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_
  · rw [adeleRing_mul_fst, infiniteAdeleInl_fst, infiniteAdeleInl_fst, adeleRing_algebraMap_fst]
  · rw [adeleRing_mul_snd, infiniteAdeleInl_snd, infiniteAdeleInl_snd, mul_zero]

theorem algebraMap_mul_finiteAdeleInr (ξ : K) (y : FiniteAdeleRing (𝓞 K) K) :
    algebraMap K 𝔸[K] ξ * finiteAdeleInr y =
      finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ * y) := by
  refine Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_
  · rw [adeleRing_mul_fst, finiteAdeleInr_fst, finiteAdeleInr_fst, mul_zero]
  · rw [adeleRing_mul_snd, finiteAdeleInr_snd, finiteAdeleInr_snd, adeleRing_algebraMap_snd]

theorem eq_of_forall_adelicChar_mul_eq {ξ η : K}
    (h : ∀ x : 𝔸[K], adelicChar K (algebraMap K 𝔸[K] ξ * x) =
      adelicChar K (algebraMap K 𝔸[K] η * x)) : ξ = η := by
  by_contra hne
  have hne' : ξ - η ≠ 0 := sub_ne_zero.mpr hne
  apply adelicChar_ne_one (K := K)
  refine DFunLike.ext _ _ fun x => ?_
  have hx : x = algebraMap K 𝔸[K] (ξ - η) * (algebraMap K 𝔸[K] (ξ - η)⁻¹ * x) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hne', map_one, one_mul]
  rw [AddChar.one_apply, hx, map_sub, sub_mul, AddChar.map_sub_eq_div, h, div_self']

theorem exists_eq_adelicChar_mul_of_integral (χ : AddChar 𝔸[K] Circle) (hχ : Continuous χ)
    (hK : ∀ k : K, χ (algebraMap K 𝔸[K] k) = 1)
    (hO : ∀ y ∈ integralFiniteAdeles (𝓞 K) K, χ (finiteAdeleInr y) = 1) :
    ∃ ξ : K, ∀ x : 𝔸[K], χ x = adelicChar K (algebraMap K 𝔸[K] ξ * x) := by
  let χM : AddChar (mixedSpace K) Circle :=
    χ.compAddMonoidHom (infiniteAdeleInl.comp (mixedToInfinite K))
  have hχM : Continuous χM :=
    hχ.comp (continuous_infiniteAdeleInl.comp continuous_mixedToInfinite)
  have hO' : ∀ a : 𝓞 K,
      χ (infiniteAdeleInl (algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K a))) = 1 := by
    intro a
    have hsplit := infiniteAdeleInl_add_finiteAdeleInr (algebraMap K 𝔸[K] (algebraMap (𝓞 K) K a))
    rw [adeleRing_algebraMap_fst, adeleRing_algebraMap_snd] at hsplit
    have h := congrArg χ hsplit
    rw [AddChar.map_add_eq_mul, hK, hO _ (algebraMap_integers_mem_integralFiniteAdeles K a),
      mul_one] at h
    exact h
  have h1 : ∀ a : 𝓞 K, χM (mixedEmbedding K (algebraMap (𝓞 K) K a)) = 1 := fun a => by
    show χ (infiniteAdeleInl (mixedToInfinite K (mixedEmbedding K _))) = 1
    rw [mixedToInfinite_mixedEmbedding]
    exact hO' a
  obtain ⟨ξ, hξO, hξ⟩ := exists_mixedSpace_char_eq χM hχM h1
  refine ⟨ξ, fun x => ?_⟩
  obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) x.2
  have hx : x = algebraMap K 𝔸[K] k + infiniteAdeleInl (x.1 - algebraMap K _ k) +
      finiteAdeleInr (x.2 - algebraMap K _ k) := by
    conv_lhs => rw [← infiniteAdeleInl_add_finiteAdeleInr x]
    refine Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_
    · simp only [adeleRing_add_fst, infiniteAdeleInl_fst, finiteAdeleInr_fst,
        adeleRing_algebraMap_fst]
      abel
    · simp only [adeleRing_add_snd, infiniteAdeleInl_snd, finiteAdeleInr_snd,
        adeleRing_algebraMap_snd]
      abel
  have hinf : ∀ z, χ (infiniteAdeleInl z) =
      adelicChar K (infiniteAdeleInl (algebraMap K (InfiniteAdeleRing K) ξ * z)) := by
    intro z
    have h := hξ (homeomorphMixedSpace K z)
    have e1 : χM (homeomorphMixedSpace K z) = χ (infiniteAdeleInl z) := by
      show χ (infiniteAdeleInl (mixedToInfinite K _)) = _
      rw [mixedToInfinite_homeomorphMixedSpace]
    rw [e1] at h
    rw [h, adelicChar_of_mem_invDifferentAdeles (mem_invDifferentAdeles.mpr
      (by rw [infiniteAdeleInl_snd]; exact zero_mem _)), infiniteAdeleInl_fst,
      ← mixedTrace_homeomorphMixedSpace]
    congr 3
    rw [homeomorphMixedSpace_apply, homeomorphMixedSpace_apply, map_mul,
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have hfin : ∀ y ∈ integralFiniteAdeles (𝓞 K) K,
      adelicChar K (finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ * y)) = 1 := by
    intro y hy
    have hξv : ∀ v : HeightOneSpectrum (𝓞 K), (ξ : v.adicCompletion K) ∈ localInvDifferent v :=
      (forall_coe_mem_localInvDifferent_iff ξ).mpr hξO
    rw [adelicChar_of_mem_invDifferentAdeles (mem_invDifferentAdeles.mpr ?_)]
    · simp
    · intro v
      show (ξ : v.adicCompletion K) * y v ∈ localInvDifferent v
      rw [mul_comm]
      exact mul_mem_localInvDifferent (hy v) (hξv v)
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [mul_add, mul_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hK, hO _ hk,
    ← (algebraMap K 𝔸[K]).map_mul, adelicChar_algebraMap, algebraMap_mul_infiniteAdeleInl,
    algebraMap_mul_finiteAdeleInr, hfin _ hk, hinf]

theorem existsUnique_eq_adelicChar_mul (χ : AddChar 𝔸[K] Circle) (hχ : Continuous χ)
    (hK : ∀ k : K, χ (algebraMap K 𝔸[K] k) = 1) :
    ∃! ξ : K, ∀ x : 𝔸[K], χ x = adelicChar K (algebraMap K 𝔸[K] ξ * x) := by
  obtain ⟨d, hd0, hd⟩ := exists_forall_finiteChar_mul_eq_one (χ.compAddMonoidHom finiteAdeleInr)
    (hχ.comp continuous_finiteAdeleInr)
  set δ : K := algebraMap (𝓞 K) K d with hδdef
  have hδ : δ ≠ 0 := by
    rw [hδdef]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  let χ' : AddChar 𝔸[K] Circle :=
    χ.compAddMonoidHom (AddMonoidHom.mulLeft (algebraMap K 𝔸[K] δ))
  have hχ' : Continuous χ' := hχ.comp (continuous_const.mul continuous_id)
  have hK' : ∀ k : K, χ' (algebraMap K 𝔸[K] k) = 1 := fun k => by
    show χ (algebraMap K 𝔸[K] δ * algebraMap K 𝔸[K] k) = 1
    rw [← map_mul, hK]
  have hO' : ∀ y ∈ integralFiniteAdeles (𝓞 K) K, χ' (finiteAdeleInr y) = 1 := fun y hy => by
    show χ (algebraMap K 𝔸[K] δ * finiteAdeleInr y) = 1
    rw [algebraMap_mul_finiteAdeleInr]
    exact hd y hy
  obtain ⟨ξ', hξ'⟩ := exists_eq_adelicChar_mul_of_integral χ' hχ' hK' hO'
  have hex : ∀ x : 𝔸[K], χ x = adelicChar K (algebraMap K 𝔸[K] (ξ' / δ) * x) := by
    intro x
    have hx : x = algebraMap K 𝔸[K] δ * (algebraMap K 𝔸[K] δ⁻¹ * x) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hδ, map_one, one_mul]
    have h := hξ' (algebraMap K 𝔸[K] δ⁻¹ * x)
    change χ (algebraMap K 𝔸[K] δ * (algebraMap K 𝔸[K] δ⁻¹ * x)) = _ at h
    rw [← hx] at h
    rw [h, ← mul_assoc, ← map_mul, div_eq_mul_inv]
  exact ⟨ξ' / δ, hex, fun η hη => eq_of_forall_adelicChar_mul_eq fun x =>
    (hη x).symm.trans (hex x)⟩

theorem existsUnique_adeleQuotient_char_eq (χ : AddChar (AdeleQuotient K) Circle)
    (hχ : Continuous χ) :
    ∃! ξ : K, ∀ x : 𝔸[K],
      χ (QuotientAddGroup.mk x) = adelicChar K (algebraMap K 𝔸[K] ξ * x) :=
  existsUnique_eq_adelicChar_mul (χ.compAddMonoidHom (QuotientAddGroup.mk' _))
    (hχ.comp continuous_quot_mk) fun k => by
      show χ (QuotientAddGroup.mk (algebraMap K 𝔸[K] k)) = 1
      have hk : algebraMap K 𝔸[K] k ∈ AdeleRing.principalSubgroup (𝓞 K) K :=
        RingHom.mem_range_self _ k
      rw [(QuotientAddGroup.eq_zero_iff _).mpr hk, AddChar.map_zero_eq_one]

theorem continuous_adelicChar_mul (ξ : K) :
    Continuous fun x : 𝔸[K] => adelicChar K (algebraMap K 𝔸[K] ξ * x) :=
  (continuous_adelicChar (K := K)).comp (continuous_const.mul continuous_id)

theorem adelicChar_mul_algebraMap (ξ k : K) :
    adelicChar K (algebraMap K 𝔸[K] ξ * algebraMap K 𝔸[K] k) = 1 := by
  rw [← map_mul, adelicChar_algebraMap]

end

end GroundTheory.Global
