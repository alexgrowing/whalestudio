import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdelicChar

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct FourierTransform

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open Classical in

def finiteAdeleSingleAdd (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →+ FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.single
    (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletionIntegers K) v x
  map_zero' := Subtype.ext (Pi.single_zero (M := fun u : HeightOneSpectrum (𝓞 K) =>
    u.adicCompletion K) v)
  map_add' x y := Subtype.ext (Pi.single_add (f := fun u : HeightOneSpectrum (𝓞 K) =>
    u.adicCompletion K) v x y)

open Classical in
theorem finiteAdeleSingleAdd_apply (v u : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingleAdd v x u =
      Pi.single (M := fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) v x u := rfl

@[simp]
theorem finiteAdeleSingleAdd_apply_self (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingleAdd v x v = x := by
  classical
  rw [finiteAdeleSingleAdd_apply]
  exact Pi.single_eq_same v x

theorem finiteAdeleSingleAdd_apply_of_ne {v u : HeightOneSpectrum (𝓞 K)} (h : u ≠ v)
    (x : v.adicCompletion K) : finiteAdeleSingleAdd v x u = 0 := by
  classical
  rw [finiteAdeleSingleAdd_apply]
  exact Pi.single_eq_of_ne h x

theorem continuous_finiteAdeleSingleAdd (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteAdeleSingleAdd (K := K) v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := by
    simp
  let g : v.adicCompletion K → Πʳ w : HeightOneSpectrum (𝓞 K),
      [w.adicCompletion K, w.adicCompletionIntegers K]_[Filter.principal {v}ᶜ] :=
    fun x ↦ ⟨Pi.single v x, Filter.eventually_principal.2 fun w hw ↦ by
      rw [Pi.single_eq_of_ne hw x]
      exact zero_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_single v)
  have hfg : (finiteAdeleSingleAdd (K := K) v : v.adicCompletion K → FiniteAdeleRing (𝓞 K) K) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

def finiteAdeleInr : FiniteAdeleRing (𝓞 K) K →+ 𝔸[K] :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
    FiniteAdeleRing (𝓞 K) K →+ InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

@[simp] theorem finiteAdeleInr_fst (a : FiniteAdeleRing (𝓞 K) K) : (finiteAdeleInr a).1 = 0 :=
  rfl

@[simp] theorem finiteAdeleInr_snd (a : FiniteAdeleRing (𝓞 K) K) : (finiteAdeleInr a).2 = a :=
  rfl

def finitePlaceIncl (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K →+ 𝔸[K] :=
  finiteAdeleInr.comp (finiteAdeleSingleAdd v)

theorem finitePlaceIncl_apply (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finitePlaceIncl v x = finiteAdeleInr (finiteAdeleSingleAdd v x) := rfl

theorem continuous_finitePlaceIncl (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finitePlaceIncl (K := K) v) :=
  continuous_const.prodMk (continuous_finiteAdeleSingleAdd v)

open Classical in

def infinitePlaceIncl (w : InfinitePlace K) : w.Completion →+ 𝔸[K] :=
  ((AddMonoidHom.single (fun u : InfinitePlace K => u.Completion) w).prod 0 :
    w.Completion →+ InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

open Classical in
theorem infinitePlaceIncl_fst (w : InfinitePlace K) (z : w.Completion) (u : InfinitePlace K) :
    (infinitePlaceIncl w z).1 u = Pi.single (M := fun u : InfinitePlace K => u.Completion) w z u :=
  rfl

@[simp] theorem infinitePlaceIncl_snd (w : InfinitePlace K) (z : w.Completion) :
    (infinitePlaceIncl w z).2 = 0 := rfl

def infiniteAdeleInl : InfiniteAdeleRing K →+ 𝔸[K] :=
  (AddMonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
    InfiniteAdeleRing K →+ InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

@[simp] theorem infiniteAdeleInl_fst (x : InfiniteAdeleRing K) : (infiniteAdeleInl x).1 = x :=
  rfl

@[simp] theorem infiniteAdeleInl_snd (x : InfiniteAdeleRing K) : (infiniteAdeleInl x).2 = 0 :=
  rfl

theorem infiniteAdeleInl_add_finiteAdeleInr (x : 𝔸[K]) :
    infiniteAdeleInl x.1 + finiteAdeleInr x.2 = x := by
  refine Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_
  · rw [adeleRing_add_fst, infiniteAdeleInl_fst, finiteAdeleInr_fst, add_zero]
  · rw [adeleRing_add_snd, infiniteAdeleInl_snd, finiteAdeleInr_snd, zero_add]

theorem continuous_infinitePlaceIncl (w : InfinitePlace K) :
    Continuous (infinitePlaceIncl (K := K) w) := by
  classical
  exact (continuous_single (A := fun u : InfinitePlace K => u.Completion) w).prodMk
    continuous_const

variable (K) in

def localAdelicChar (v : HeightOneSpectrum (𝓞 K)) : AddChar (v.adicCompletion K) Circle :=
  (adelicChar K).compAddMonoidHom (finitePlaceIncl v)

variable (K) in

def infiniteAdelicChar (w : InfinitePlace K) : AddChar w.Completion Circle :=
  (adelicChar K).compAddMonoidHom (infinitePlaceIncl w)

theorem localAdelicChar_apply (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K) :
    localAdelicChar K v y = adelicChar K (finitePlaceIncl v y) := rfl

theorem infiniteAdelicChar_apply' (w : InfinitePlace K) (z : w.Completion) :
    infiniteAdelicChar K w z = adelicChar K (infinitePlaceIncl w z) := rfl

theorem continuous_localAdelicChar (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localAdelicChar K v) :=
  (continuous_adelicChar (K := K)).comp (continuous_finitePlaceIncl v)

theorem continuous_infiniteAdelicChar (w : InfinitePlace K) :
    Continuous (infiniteAdelicChar K w) :=
  (continuous_adelicChar (K := K)).comp (continuous_infinitePlaceIncl w)

theorem infiniteAdelicChar_apply (w : InfinitePlace K) (z : w.Completion) :
    infiniteAdelicChar K w z = 𝐞 (-((w.mult : ℝ) * (extensionEmbedding w z).re)) := by
  classical
  rw [infiniteAdelicChar_apply', adelicChar_of_mem_invDifferentAdeles
    (mem_invDifferentAdeles.mpr (by rw [infinitePlaceIncl_snd]; exact zero_mem _)),
    infiniteTrace_apply, Finset.sum_eq_single w]
  · rw [infinitePlaceIncl_fst, Pi.single_eq_same]
  · intro u _ hu
    rw [infinitePlaceIncl_fst, Pi.single_eq_of_ne hu, map_zero, Complex.zero_re, mul_zero]
  · simp

theorem infiniteAdelicChar_apply_of_isReal {w : InfinitePlace K} (hw : IsReal w)
    (z : w.Completion) : infiniteAdelicChar K w z = 𝐞 (-extensionEmbeddingOfIsReal hw z) := by
  rw [infiniteAdelicChar_apply, hw.mult_eq_one, ← extensionEmbeddingOfIsReal_apply hw,
    Complex.ofReal_re, Nat.cast_one, one_mul]

theorem infiniteAdelicChar_apply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w)
    (z : w.Completion) :
    infiniteAdelicChar K w z = 𝐞 (-(2 * (extensionEmbedding w z).re)) := by
  rw [infiniteAdelicChar_apply, hw.mult_eq_two, Nat.cast_ofNat]

theorem addChar_map_finsetSum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A Circle)
    (s : Finset ι) (f : ι → A) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem adelicChar_infiniteAdeleInl (x : InfiniteAdeleRing K) :
    adelicChar K (infiniteAdeleInl x) = ∏ w : InfinitePlace K, infiniteAdelicChar K w (x w) := by
  rw [adelicChar_of_mem_invDifferentAdeles
    (mem_invDifferentAdeles.mpr (by rw [infiniteAdeleInl_snd]; exact zero_mem _)),
    infiniteAdeleInl_fst, infiniteTrace_apply, ← Finset.sum_neg_distrib, addChar_map_finsetSum]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [infiniteAdelicChar_apply]

theorem coe_sub_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (a b : K) :
    ((a - b : K) : v.adicCompletion K) = (a : v.adicCompletion K) - (b : v.adicCompletion K) := by
  have hc : ∀ z : K, (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z :=
    fun z => by simp [algebraMap_adicCompletion]
  rw [hc, hc, hc, map_sub]

theorem exists_sub_mem_adicCompletionIntegers_and_forall_ne (v : HeightOneSpectrum (𝓞 K))
    (y : v.adicCompletion K) :
    ∃ k : K, y - k ∈ v.adicCompletionIntegers K ∧
      ∀ u ≠ v, (k : u.adicCompletion K) ∈ u.adicCompletionIntegers K := by
  classical
  have hU : IsOpen {z : v.adicCompletion K | y - z ∈ v.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
      (continuous_const.sub continuous_id)
  obtain ⟨z, hz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU ⟨y, by simp⟩
  obtain ⟨k, hkS, hkn⟩ := exists_valuation_sub_le_one {v} (fun _ => z)
  refine ⟨k, ?_, fun u hu => ?_⟩
  · have h1 := (coe_mem_adicCompletionIntegers_iff v (k - z)).mpr (hkS v (Finset.mem_singleton_self v))
    have h2 : y - (k : v.adicCompletion K) =
        (y - (z : v.adicCompletion K)) - ((k - z : K) : v.adicCompletion K) := by
      rw [coe_sub_adicCompletion]
      ring
    rw [h2]
    have hz' : y - (z : v.adicCompletion K) ∈ v.adicCompletionIntegers K := hz
    exact sub_mem hz' h1
  · exact (coe_mem_adicCompletionIntegers_iff u k).mpr (hkn u (by simpa using hu))

theorem localAdelicChar_eq_one_of_mem {v : HeightOneSpectrum (𝓞 K)} {y : v.adicCompletion K}
    (hy : y ∈ localInvDifferent v) : localAdelicChar K v y = 1 := by
  rw [localAdelicChar_apply, adelicChar_of_mem_invDifferentAdeles]
  · simp [finitePlaceIncl_apply]
  · refine mem_invDifferentAdeles.mpr fun u => ?_
    rw [finitePlaceIncl_apply, finiteAdeleInr_snd]
    by_cases hu : u = v
    · subst hu
      rwa [finiteAdeleSingleAdd_apply_self]
    · rw [finiteAdeleSingleAdd_apply_of_ne hu]
      exact zero_mem _

theorem localAdelicChar_eq (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K) {k : K}
    (hk : y - k ∈ localInvDifferent v)
    (hk' : ∀ u ≠ v, (k : u.adicCompletion K) ∈ localInvDifferent u) :
    localAdelicChar K v y = 𝐞 (Algebra.trace ℚ K k) := by
  rw [localAdelicChar_apply, adelicChar_eq (k := k)]
  · rw [finitePlaceIncl_apply, finiteAdeleInr_fst, zero_sub, map_neg (infiniteTrace K), neg_neg,
      infiniteTrace_algebraMap]
  · intro u
    show finiteAdeleSingleAdd v y u - (k : u.adicCompletion K) ∈ localInvDifferent u
    by_cases hu : u = v
    · subst hu
      rwa [finiteAdeleSingleAdd_apply_self]
    · rw [finiteAdeleSingleAdd_apply_of_ne hu, zero_sub]
      exact neg_mem (hk' u hu)

theorem localAdelicChar_coe (v : HeightOneSpectrum (𝓞 K)) {k : K}
    (hk' : ∀ u ≠ v, (k : u.adicCompletion K) ∈ localInvDifferent u) :
    localAdelicChar K v k = 𝐞 (Algebra.trace ℚ K k) :=
  localAdelicChar_eq v _ (by rw [sub_self]; exact zero_mem _) hk'

theorem exists_localAdelicChar_eq (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K) :
    ∃ k : K, y - k ∈ v.adicCompletionIntegers K ∧
      (∀ u ≠ v, (k : u.adicCompletion K) ∈ u.adicCompletionIntegers K) ∧
      localAdelicChar K v y = 𝐞 (Algebra.trace ℚ K k) := by
  obtain ⟨k, hk, hk'⟩ := exists_sub_mem_adicCompletionIntegers_and_forall_ne v y
  exact ⟨k, hk, hk', localAdelicChar_eq v y (mem_localInvDifferent_of_mem hk)
    fun u hu => mem_localInvDifferent_of_mem (hk' u hu)⟩

theorem forall_localAdelicChar_mul_eq_one_iff (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) :
    (∀ a ∈ v.adicCompletionIntegers K, localAdelicChar K v (a * x) = 1) ↔
      x ∈ localInvDifferent v := by
  refine ⟨fun h => ?_, fun hx a ha => localAdelicChar_eq_one_of_mem
    (mul_mem_localInvDifferent ha hx)⟩
  obtain ⟨k, hk, hk'⟩ := exists_sub_mem_adicCompletionIntegers_and_forall_ne v x
  have htr : ∀ a : 𝓞 K,
      Algebra.trace ℚ K (k * algebraMap (𝓞 K) K a) ∈ (algebraMap ℤ ℚ).range := by
    intro a
    have hb' : ∀ u ≠ v, ((k * algebraMap (𝓞 K) K a : K) : u.adicCompletion K) ∈
        localInvDifferent u := fun u hu => mem_localInvDifferent_of_mem (by
      rw [coe_mul_adicCompletion]
      exact mul_mem (hk' u hu) (coe_algebraMap_mem_adicCompletionIntegers u a))
    have h1 := localAdelicChar_coe v hb'
    have hbx : ((k * algebraMap (𝓞 K) K a : K) : v.adicCompletion K) =
        ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) * x -
          ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) * (x - k) := by
      rw [coe_mul_adicCompletion]
      ring
    rw [hbx, AddChar.map_sub_eq_div, h _ (coe_algebraMap_mem_adicCompletionIntegers v a),
      localAdelicChar_eq_one_of_mem (mul_mem_localInvDifferent
        (coe_algebraMap_mem_adicCompletionIntegers v a) (mem_localInvDifferent_of_mem hk)),
      div_one, eq_comm, fourierChar_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by exact_mod_cast hn.symm⟩
  have hk_mem := (forall_mul_mem_iff_forall_trace_mem K k).mpr htr
  intro y hy
  obtain ⟨z, hz⟩ := hk_mem y hy
  have : x * ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) =
      ((k * algebraMap (𝓞 K) K y : K) : v.adicCompletion K) +
        (x - k) * ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) := by
    rw [coe_mul_adicCompletion]
    ring
  rw [this, ← hz]
  exact add_mem (coe_algebraMap_mem_adicCompletionIntegers v z)
    (mul_mem hk (coe_algebraMap_mem_adicCompletionIntegers v y))

theorem forall_localAdelicChar_eq_one_iff_le (v : HeightOneSpectrum (𝓞 K))
    (M : AddSubgroup (v.adicCompletion K))
    (hM : ∀ a ∈ v.adicCompletionIntegers K, ∀ x ∈ M, a * x ∈ M) :
    (∀ x ∈ M, localAdelicChar K v x = 1) ↔ M ≤ localInvDifferent v :=
  ⟨fun h x hx => (forall_localAdelicChar_mul_eq_one_iff v x).mp fun a ha => h _ (hM a ha x hx),
    fun h _ hx => localAdelicChar_eq_one_of_mem (h hx)⟩

theorem finite_mulSupport_localAdelicChar (x : 𝔸[K]) :
    (Function.mulSupport fun v => localAdelicChar K v (x.2 v)).Finite :=
  (Filter.eventually_cofinite.mp x.2.2).subset fun _ hv hO =>
    hv (localAdelicChar_eq_one_of_mem (mem_localInvDifferent_of_mem hO))

theorem adelicChar_eq_prod (x : 𝔸[K]) :
    adelicChar K x = (∏ w : InfinitePlace K, infiniteAdelicChar K w (x.1 w)) *
      ∏ᶠ v, localAdelicChar K v (x.2 v) := by
  classical
  have hS := Filter.eventually_cofinite.mp x.2.2
  set S := hS.toFinset
  have hmemS : ∀ u, u ∉ S → x.2 u ∈ u.adicCompletionIntegers K := fun u hu => by
    have h := hu
    simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h
    exact h
  obtain ⟨f, hfdef⟩ : ∃ f : FiniteAdeleRing (𝓞 K) K,
      f = ∑ v ∈ S, finiteAdeleSingleAdd v (x.2 v) := ⟨_, rfl⟩
  have hrest : x.2 - f ∈ finiteInvDifferent K := by
    intro u
    have hsum : f u = ∑ v ∈ S, finiteAdeleSingleAdd v (x.2 v) u := hfdef ▸
      map_sum (RestrictedProduct.evalAddMonoidHom
        (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) u) _ S
    show x.2 u - f u ∈ localInvDifferent u
    rw [hsum]
    by_cases hu : u ∈ S
    · rw [Finset.sum_eq_single_of_mem u hu (fun v _ hv => finiteAdeleSingleAdd_apply_of_ne
        (Ne.symm hv) _), finiteAdeleSingleAdd_apply_self, sub_self]
      exact zero_mem _
    · rw [Finset.sum_eq_zero (fun v hv => finiteAdeleSingleAdd_apply_of_ne
        (by rintro rfl; exact hu hv) _), sub_zero]
      exact mem_localInvDifferent_of_mem (hmemS u hu)
  have hf : finiteAdeleInr f + finiteAdeleInr (x.2 - f) = finiteAdeleInr (K := K) x.2 := by
    rw [← map_add, add_sub_cancel]
  have hx : x = infiniteAdeleInl x.1 + finiteAdeleInr f + finiteAdeleInr (x.2 - f) := by
    rw [add_assoc, hf, infiniteAdeleInl_add_finiteAdeleInr]
  have h1 : adelicChar K (finiteAdeleInr (x.2 - f)) = 1 := by
    rw [adelicChar_of_mem_invDifferentAdeles
      (mem_invDifferentAdeles.mpr (by rw [finiteAdeleInr_snd]; exact hrest)),
      finiteAdeleInr_fst, map_zero, neg_zero, AddChar.map_zero_eq_one]
  have h2 : adelicChar K (finiteAdeleInr f) = ∏ v ∈ S, localAdelicChar K v (x.2 v) := by
    rw [hfdef, map_sum, addChar_map_finsetSum]
    rfl
  have h3 : ∏ᶠ v, localAdelicChar K v (x.2 v) = ∏ v ∈ S, localAdelicChar K v (x.2 v) := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS
    exact hv (localAdelicChar_eq_one_of_mem (mem_localInvDifferent_of_mem (hmemS v hvS)))
  conv_lhs => rw [hx]
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1, mul_one, h2, h3,
    adelicChar_infiniteAdeleInl]

end

end GroundTheory.Global
