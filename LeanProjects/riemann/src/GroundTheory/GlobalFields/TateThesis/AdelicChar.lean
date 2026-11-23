import Mathlib
import GroundTheory.GlobalFields.Adele.Approximation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfiniteTraceAlgebraMap

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct FourierTransform nonZeroDivisors

noncomputable section

theorem fourierChar_eq_one_iff (t : ℝ) : 𝐞 t = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) ?_⟩
    rw [hn]
    ring
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem fourierChar_intCast (n : ℤ) : 𝐞 (n : ℝ) = 1 :=
  (fourierChar_eq_one_iff _).mpr ⟨n, rfl⟩

variable (K : Type*) [Field K] [NumberField K]

def infiniteTrace : InfiniteAdeleRing K →+ ℝ where
  toFun x := ∑ w : InfinitePlace K, (w.mult : ℝ) * (extensionEmbedding w (x w)).re
  map_zero' := by
    refine Finset.sum_eq_zero fun w _ => ?_
    show (w.mult : ℝ) * (extensionEmbedding w 0).re = 0
    simp
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    show (w.mult : ℝ) * (extensionEmbedding w (x w + y w)).re = _
    rw [map_add, Complex.add_re, mul_add]

theorem infiniteTrace_apply (x : InfiniteAdeleRing K) :
    infiniteTrace K x = ∑ w : InfinitePlace K, (w.mult : ℝ) * (extensionEmbedding w (x w)).re :=
  rfl

theorem continuous_infiniteTrace : Continuous (infiniteTrace K) := by
  show Continuous fun x : InfiniteAdeleRing K =>
    ∑ w : InfinitePlace K, (w.mult : ℝ) * (extensionEmbedding w (x w)).re
  exact continuous_finsetSum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp
    ((isometry_extensionEmbedding w).continuous.comp (continuous_apply w)))

omit [NumberField K] in
theorem extensionEmbedding_algebraMap_apply (k : K) (w : InfinitePlace K) :
    extensionEmbedding w (algebraMap K (InfiniteAdeleRing K) k w) = w.embedding k := by
  simp [InfiniteAdeleRing.algebraMap_apply]

theorem infiniteTrace_algebraMap (k : K) :
    infiniteTrace K (algebraMap K (InfiniteAdeleRing K) k) = (Algebra.trace ℚ K k : ℝ) :=
  by apply _root_.UpperTheory.Reformulated.B.Qh34.infiniteTrace_algebraMap <;> assumption

theorem forall_mul_mem_iff_forall_trace_mem (k : K) :
    (∀ y ∈ differentIdeal ℤ (𝓞 K), k * algebraMap (𝓞 K) K y ∈ (algebraMap (𝓞 K) K).range) ↔
      ∀ a : 𝓞 K, Algebra.trace ℚ K (k * algebraMap (𝓞 K) K a) ∈ (algebraMap ℤ ℚ).range := by
  have hd := coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
  have hdual0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hD0 : ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [hd]
    exact inv_ne_zero hdual0
  have key : k ∈ ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ↔
      k ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hd, inv_inv]
  rw [FractionalIdeal.mem_inv_iff hD0,
    FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)] at key
  constructor
  · intro h a
    have := key.mp (fun y hy => ?_) (algebraMap (𝓞 K) K a) ?_
    · simpa [Algebra.traceForm_apply] using this
    · obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
      obtain ⟨z, hz⟩ := h y' hy'
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨z, hz⟩
    · exact (FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩
  · intro h y hy
    have := key.mpr (fun b hb => ?_) (algebraMap (𝓞 K) K y)
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hy, rfl⟩)
    · obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).mp this
      exact ⟨z, hz⟩
    · obtain ⟨b', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hb
      simpa [Algebra.traceForm_apply] using h b'

variable {K}

def localInvDifferent (v : HeightOneSpectrum (𝓞 K)) : AddSubgroup (v.adicCompletion K) where
  carrier := {x | ∀ y ∈ differentIdeal ℤ (𝓞 K),
    x * ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K}
  zero_mem' := fun y _ => by
    rw [zero_mul]
    exact zero_mem _
  add_mem' := fun ha hb y hy => by
    rw [add_mul]
    exact add_mem (ha y hy) (hb y hy)
  neg_mem' := fun ha y hy => by
    rw [neg_mul]
    exact neg_mem (ha y hy)

theorem mem_localInvDifferent {v : HeightOneSpectrum (𝓞 K)} {x : v.adicCompletion K} :
    x ∈ localInvDifferent v ↔ ∀ y ∈ differentIdeal ℤ (𝓞 K),
      x * ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem coe_algebraMap_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) :
    ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [coe_mem_adicCompletionIntegers_iff, valuation_of_algebraMap]
  exact v.intValuation_le_one y

theorem coe_mul_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (a b : K) :
    ((a * b : K) : v.adicCompletion K) = (a : v.adicCompletion K) * (b : v.adicCompletion K) := by
  have hc : ∀ z : K, (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z :=
    fun z => by simp [algebraMap_adicCompletion]
  rw [hc, hc, hc, map_mul]

theorem mem_localInvDifferent_of_mem {v : HeightOneSpectrum (𝓞 K)} {x : v.adicCompletion K}
    (hx : x ∈ v.adicCompletionIntegers K) : x ∈ localInvDifferent v :=
  fun y _ => mul_mem hx (coe_algebraMap_mem_adicCompletionIntegers v y)

theorem mul_mem_localInvDifferent {v : HeightOneSpectrum (𝓞 K)} {a x : v.adicCompletion K}
    (ha : a ∈ v.adicCompletionIntegers K) (hx : x ∈ localInvDifferent v) :
    a * x ∈ localInvDifferent v :=
  fun y hy => by
    rw [mul_assoc]
    exact mul_mem ha (hx y hy)

theorem isOpen_localInvDifferent (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (localInvDifferent v : Set (v.adicCompletion K)) :=
  AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset
    ((Valued.isOpen_valuationSubring (v.adicCompletion K)).mem_nhds (zero_mem _))
    fun _ hx => mem_localInvDifferent_of_mem hx)

theorem coe_mem_localInvDifferent_iff (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    (k : v.adicCompletion K) ∈ localInvDifferent v ↔
      ∀ y ∈ differentIdeal ℤ (𝓞 K), v.valuation K (k * algebraMap (𝓞 K) K y) ≤ 1 := by
  refine forall₂_congr fun y _ => ?_
  rw [← coe_mul_adicCompletion, coe_mem_adicCompletionIntegers_iff]

theorem forall_coe_mem_localInvDifferent_iff (k : K) :
    (∀ v : HeightOneSpectrum (𝓞 K), (k : v.adicCompletion K) ∈ localInvDifferent v) ↔
      ∀ a : 𝓞 K, Algebra.trace ℚ K (k * algebraMap (𝓞 K) K a) ∈ (algebraMap ℤ ℚ).range := by
  rw [← forall_mul_mem_iff_forall_trace_mem]
  simp_rw [coe_mem_localInvDifferent_iff]
  constructor
  · intro h y hy
    exact mem_integers_of_valuation_le_one (R := 𝓞 K) K _ fun v => h v y hy
  · intro h v y hy
    obtain ⟨z, hz⟩ := h y hy
    rw [← hz, valuation_of_algebraMap]
    exact v.intValuation_le_one z

@[simp] theorem adeleRing_add_fst (x y : 𝔸[K]) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem adeleRing_add_snd (x y : 𝔸[K]) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem adeleRing_sub_fst (x y : 𝔸[K]) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem adeleRing_sub_snd (x y : 𝔸[K]) : (x - y).2 = x.2 - y.2 := rfl
@[simp] theorem adeleRing_zero_fst : (0 : 𝔸[K]).1 = 0 := rfl
@[simp] theorem adeleRing_zero_snd : (0 : 𝔸[K]).2 = 0 := rfl
@[simp] theorem adeleRing_algebraMap_fst (k : K) :
    (algebraMap K 𝔸[K] k).1 = algebraMap K (InfiniteAdeleRing K) k := rfl
@[simp] theorem adeleRing_algebraMap_snd (k : K) :
    (algebraMap K 𝔸[K] k).2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) k := rfl

variable (K) in

def finiteInvDifferent : AddSubgroup (FiniteAdeleRing (𝓞 K) K) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ localInvDifferent v}
  zero_mem' v := zero_mem (localInvDifferent v)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  neg_mem' ha v := neg_mem (ha v)

theorem mem_finiteInvDifferent {a : FiniteAdeleRing (𝓞 K) K} :
    a ∈ finiteInvDifferent K ↔ ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ localInvDifferent v :=
  Iff.rfl

theorem mem_finiteInvDifferent_of_mem_integralFiniteAdeles {a : FiniteAdeleRing (𝓞 K) K}
    (ha : a ∈ integralFiniteAdeles (𝓞 K) K) : a ∈ finiteInvDifferent K :=
  fun v => mem_localInvDifferent_of_mem (ha v)

variable (K) in

theorem isOpen_finiteInvDifferent :
    IsOpen (finiteInvDifferent K : Set (FiniteAdeleRing (𝓞 K) K)) :=
  AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset
    ((isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K)).mem_nhds (zero_mem _))
    fun _ ha => mem_finiteInvDifferent_of_mem_integralFiniteAdeles ha)

theorem exists_sub_mem_finiteInvDifferent (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ k : K, a - algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ finiteInvDifferent K := by
  obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) a
  exact ⟨k, mem_finiteInvDifferent_of_mem_integralFiniteAdeles hk⟩

theorem algebraMap_mem_finiteInvDifferent_iff (k : K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ finiteInvDifferent K ↔
      ∀ a : 𝓞 K, Algebra.trace ℚ K (k * algebraMap (𝓞 K) K a) ∈ (algebraMap ℤ ℚ).range :=
  forall_coe_mem_localInvDifferent_iff k

theorem exists_trace_eq_intCast {k : K}
    (hk : algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ finiteInvDifferent K) :
    ∃ n : ℤ, (Algebra.trace ℚ K k : ℝ) = n := by
  obtain ⟨n, hn⟩ := (algebraMap_mem_finiteInvDifferent_iff k).mp hk 1
  refine ⟨n, ?_⟩
  rw [map_one, mul_one] at hn
  rw [← hn]
  simp

variable (K) in

def invDifferentAdeles : AddSubgroup 𝔸[K] :=
  (⊤ : AddSubgroup (InfiniteAdeleRing K)).prod (finiteInvDifferent K)

theorem mem_invDifferentAdeles {x : 𝔸[K]} :
    x ∈ invDifferentAdeles K ↔ x.2 ∈ finiteInvDifferent K := by
  exact ⟨fun h => h.2, fun h => ⟨AddSubgroup.mem_top _, h⟩⟩

variable (K) in

theorem isOpen_invDifferentAdeles : IsOpen (invDifferentAdeles K : Set 𝔸[K]) := by
  have : (invDifferentAdeles K : Set 𝔸[K]) =
      Prod.snd ⁻¹' (finiteInvDifferent K : Set (FiniteAdeleRing (𝓞 K) K)) := by
    ext x
    exact mem_invDifferentAdeles
  rw [this]
  exact (isOpen_finiteInvDifferent K).preimage continuous_snd

theorem exists_sub_mem_invDifferentAdeles (x : 𝔸[K]) :
    ∃ k : K, x - algebraMap K 𝔸[K] k ∈ invDifferentAdeles K := by
  obtain ⟨k, hk⟩ := exists_sub_mem_finiteInvDifferent x.2
  exact ⟨k, mem_invDifferentAdeles.mpr hk⟩

theorem algebraMap_mem_invDifferentAdeles_iff (k : K) :
    algebraMap K 𝔸[K] k ∈ invDifferentAdeles K ↔
      k ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
  rw [mem_invDifferentAdeles, Submodule.mem_traceDual]
  refine (algebraMap_mem_finiteInvDifferent_iff k).trans ⟨fun h a ha => ?_, fun h a => ?_⟩
  · obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    simpa [Algebra.traceForm_apply] using h b
  · simpa [Algebra.traceForm_apply] using h _ (Submodule.mem_one.mpr ⟨a, rfl⟩)

theorem fourierChar_infiniteTrace_eq (x : InfiniteAdeleRing K) (a : FiniteAdeleRing (𝓞 K) K)
    {k k' : K} (hk : a - algebraMap K _ k ∈ finiteInvDifferent K)
    (hk' : a - algebraMap K _ k' ∈ finiteInvDifferent K) :
    𝐞 (-infiniteTrace K (x - algebraMap K _ k)) = 𝐞 (-infiniteTrace K (x - algebraMap K _ k')) := by
  have hd : algebraMap K (FiniteAdeleRing (𝓞 K) K) (k' - k) ∈ finiteInvDifferent K := by
    have := sub_mem hk hk'
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  obtain ⟨n, hn⟩ := exists_trace_eq_intCast hd
  have : -infiniteTrace K (x - algebraMap K _ k) =
      -infiniteTrace K (x - algebraMap K _ k') - n := by
    rw [← hn, ← infiniteTrace_algebraMap]
    simp only [map_sub]
    ring
  rw [this, AddChar.map_sub_eq_div, fourierChar_intCast, div_one]

variable (K) in

def adelicCharFun (x : 𝔸[K]) : Circle :=
  𝐞 (-infiniteTrace K (x.1 - algebraMap K _ (exists_sub_mem_finiteInvDifferent x.2).choose))

theorem adelicCharFun_eq (x : 𝔸[K]) {k : K}
    (hk : x.2 - algebraMap K _ k ∈ finiteInvDifferent K) :
    adelicCharFun K x = 𝐞 (-infiniteTrace K (x.1 - algebraMap K _ k)) :=
  fourierChar_infiniteTrace_eq _ _ (exists_sub_mem_finiteInvDifferent x.2).choose_spec hk

variable (K) in

def adelicChar : AddChar 𝔸[K] Circle where
  toFun := adelicCharFun K
  map_zero_eq_one' := by
    rw [adelicCharFun_eq (k := 0) 0 (by simp)]
    simp
  map_add_eq_mul' x y := by
    obtain ⟨kx, hx⟩ := exists_sub_mem_finiteInvDifferent x.2
    obtain ⟨ky, hy⟩ := exists_sub_mem_finiteInvDifferent y.2
    have hxy : (x + y).2 - algebraMap K _ (kx + ky) ∈ finiteInvDifferent K := by
      have := add_mem hx hy
      rw [map_add]
      convert this using 1
      rw [adeleRing_add_snd]
      abel
    rw [adelicCharFun_eq _ hxy, adelicCharFun_eq _ hx, adelicCharFun_eq _ hy,
      ← AddChar.map_add_eq_mul]
    congr 1
    simp only [adeleRing_add_fst, map_add, map_sub]
    ring

theorem adelicChar_apply (x : 𝔸[K]) : adelicChar K x = adelicCharFun K x := rfl

theorem adelicChar_eq (x : 𝔸[K]) {k : K}
    (hk : x.2 - algebraMap K _ k ∈ finiteInvDifferent K) :
    adelicChar K x = 𝐞 (-infiniteTrace K (x.1 - algebraMap K _ k)) :=
  adelicCharFun_eq x hk

theorem adelicChar_algebraMap_add (a : K) {y : 𝔸[K]} (hy : y ∈ invDifferentAdeles K) :
    adelicChar K (algebraMap K 𝔸[K] a + y) = 𝐞 (-infiniteTrace K y.1) := by
  rw [adelicChar_eq (k := a)]
  · congr 3
    show algebraMap K (InfiniteAdeleRing K) a + y.1 - algebraMap K _ a = y.1
    abel
  · show algebraMap K (FiniteAdeleRing (𝓞 K) K) a + y.2 - algebraMap K _ a ∈ _
    rw [add_sub_cancel_left]
    exact mem_invDifferentAdeles.mp hy

theorem adelicChar_of_mem_invDifferentAdeles {y : 𝔸[K]} (hy : y ∈ invDifferentAdeles K) :
    adelicChar K y = 𝐞 (-infiniteTrace K y.1) := by
  simpa using adelicChar_algebraMap_add (0 : K) hy

theorem adelicChar_algebraMap (k : K) : adelicChar K (algebraMap K 𝔸[K] k) = 1 := by
  simpa using adelicChar_algebraMap_add k (zero_mem (invDifferentAdeles K))

theorem adelicChar_infinite (x : InfiniteAdeleRing K) :
    adelicChar K ((x, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) =
      𝐞 (-infiniteTrace K x) :=
  adelicChar_of_mem_invDifferentAdeles (mem_invDifferentAdeles.mpr (zero_mem _))

theorem continuous_adelicChar : Continuous (adelicChar K) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨k, hk⟩ := exists_sub_mem_finiteInvDifferent x0.2
  have hU : IsOpen {x : 𝔸[K] | x.2 - algebraMap K _ k ∈ finiteInvDifferent K} :=
    (isOpen_finiteInvDifferent K).preimage (continuous_snd.sub continuous_const)
  have heq : (fun x : 𝔸[K] => 𝐞 (-infiniteTrace K (x.1 - algebraMap K _ k))) =ᶠ[𝓝 x0]
      adelicChar K :=
    Filter.eventually_of_mem (hU.mem_nhds hk) fun x hx => (adelicChar_eq x hx).symm
  refine ContinuousAt.congr ?_ heq
  exact (Real.continuous_fourierChar.comp ((continuous_infiniteTrace K).comp
    (continuous_fst.sub continuous_const)).neg).continuousAt

theorem adelicChar_ne_one : adelicChar K ≠ 1 := by
  intro h
  set n := Module.finrank ℚ K with hn
  have hn0 : (n : ℚ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    exact_mod_cast this.ne'
  have htr : Algebra.trace ℚ K (algebraMap ℚ K (1 / (2 * n))) = 1 / 2 := by
    rw [Algebra.trace_algebraMap, ← hn, nsmul_eq_mul]
    field_simp
  have h1 : adelicChar K
      ((algebraMap K (InfiniteAdeleRing K) (algebraMap ℚ K (1 / (2 * n))), 0) :
        InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) = 1 := by
    rw [h]
    rfl
  rw [adelicChar_infinite, infiniteTrace_algebraMap, htr, fourierChar_eq_one_iff] at h1
  obtain ⟨m, hm⟩ := h1
  have : (2 * m : ℝ) = -1 := by
    push_cast at hm
    linarith
  have : (2 * m : ℤ) = -1 := by exact_mod_cast this
  omega

end

end GroundTheory.Global
