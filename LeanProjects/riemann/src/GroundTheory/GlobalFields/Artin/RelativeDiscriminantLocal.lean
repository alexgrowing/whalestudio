import Mathlib
import GroundTheory.GlobalFields.Artin.RelativeDiscriminant
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.Different
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField

open scoped WithZero

namespace GroundTheory.Global

section Local

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion M)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)]

theorem mem_inv_maximalIdeal_pow_iff {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : u.adicCompletion F) :
    y ∈ ((𝓂[u.adicCompletion F] ^ n : Ideal 𝒪[u.adicCompletion F]) :
      FractionalIdeal (nonZeroDivisors 𝒪[u.adicCompletion F]) (u.adicCompletion F))⁻¹ ↔
      Valued.v y ≤ WithZero.exp (n : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[u.adicCompletion F]
  have hv : Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1) :=
    valued_of_irreducible_integer u hϖ
  have hvn : Valued.v ((ϖ : u.adicCompletion F) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hv, ← WithZero.exp_nsmul]
    simp
  have hϖ0 : ((ϖ : u.adicCompletion F) ^ n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvn
    exact WithZero.zero_ne_coe hvn
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_spanSingleton]
  change (∃ b : 𝒪[u.adicCompletion F], (b : u.adicCompletion F) *
    ((ϖ : u.adicCompletion F) ^ n)⁻¹ = y) ↔ _
  constructor
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_inv₀, hvn, WithZero.exp_neg, inv_inv]
    exact mul_le_of_le_one_left zero_le ((integers_valued u).map_le_one b)
  · intro hy
    have hb : Valued.v (y * (ϖ : u.adicCompletion F) ^ n) ≤ 1 := by
      rw [map_mul, hvn]
      calc Valued.v y * WithZero.exp (-(n : ℤ))
          ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) := by gcongr
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    refine ⟨⟨_, (mem_valuationInteger_iff u _).2 hb⟩, ?_⟩
    change y * (ϖ : u.adicCompletion F) ^ n * ((ϖ : u.adicCompletion F) ^ n)⁻¹ = y
    rw [mul_assoc, mul_inv_cancel₀ hϖ0, mul_one]

theorem forall_valued_trace_le_one_iff (n : ℕ) :
    (∀ y : w.adicCompletion M, Valued.v y ≤ WithZero.exp (n : ℤ) →
      Valued.v (Algebra.trace (v.adicCompletion K) (w.adicCompletion M) y) ≤ 1) ↔
      n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  have hI : (𝓂[w.adicCompletion M] ^ n) ≠ ⊥ :=
    pow_ne_zero _ (IsDiscreteValuationRing.not_a_field _)
  rw [← maximalIdeal_pow_dvd_pow_iff (R := 𝒪[w.adicCompletion M]),
    ← differentIdeal_eq_maximalIdeal_pow, Ideal.dvd_iff_le,
    differentialIdeal_le_iff (K := v.adicCompletion K) (L := w.adicCompletion M) hI,
    Submodule.map_le_iff_le_comap]
  constructor
  · intro h y hy
    have hy' := h y ((mem_inv_maximalIdeal_pow_iff w n y).1 hy)
    rw [Submodule.mem_comap]
    exact Submodule.mem_one.2 ⟨⟨_, (mem_valuationInteger_iff v _).2 hy'⟩, rfl⟩
  · intro h y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (Submodule.mem_comap.1
      (h ((mem_inv_maximalIdeal_pow_iff w n y).2 hy)))
    change (a : v.adicCompletion K) = Algebra.trace (v.adicCompletion K) (w.adicCompletion M) y
      at ha
    rw [← ha]
    exact (integers_valued v).map_le_one a

end Local

section Global

variable {M : Type*} [Field M] [NumberField M]

theorem mem_inv_pow_iff (w : HeightOneSpectrum (𝓞 M)) (n : ℕ) (x : M) :
    x ∈ ((w.asIdeal ^ n : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ↔
      w.valuation M x ≤ WithZero.exp (n : ℤ) ∧
        ∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M x ≤ 1 := by
  have hI : ((w.asIdeal ^ n : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact pow_ne_zero _ w.ne_bot
  rw [FractionalIdeal.mem_inv_iff hI]
  constructor
  · intro h
    have key : ∀ y ∈ w.asIdeal ^ n, ∀ u : HeightOneSpectrum (𝓞 M),
        u.valuation M x * u.intValuation y ≤ 1 := by
      intro y hy u
      obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 M))).1
        (h _ ((FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 M))).2 ⟨y, hy, rfl⟩))
      rw [← valuation_of_algebraMap (K := M), ← map_mul, ← hb, valuation_of_algebraMap]
      exact u.intValuation_le_one b
    refine ⟨?_, fun u hu ↦ ?_⟩
    · obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
      have hπn : w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
        rw [map_pow, hπ, ← WithZero.exp_nsmul]
        simp
      have hmem : π ^ n ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem _ n).1 hπn.le
      have h1 := key _ hmem w
      rw [hπn] at h1
      calc w.valuation M x
          = w.valuation M x * WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) := by
            rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
        _ ≤ 1 * WithZero.exp (n : ℤ) := by gcongr
        _ = WithZero.exp (n : ℤ) := one_mul _
    · have hnle : ¬ w.asIdeal ^ n ≤ u.asIdeal := by
        intro hle
        have hwu : w.asIdeal ≤ u.asIdeal := u.isPrime.le_of_pow_le hle
        exact hu (HeightOneSpectrum.ext
          ((w.isMaximal.eq_of_le u.isPrime.ne_top hwu).symm))
      obtain ⟨y, hy, hyu⟩ := SetLike.not_le_iff_exists.1 hnle
      have h1 := key y hy u
      have hy1 : u.intValuation y = 1 := le_antisymm (u.intValuation_le_one y)
        (not_lt.1 fun hlt ↦ hyu ((u.intValuation_lt_one_iff_mem y).1 hlt))
      rwa [hy1, mul_one] at h1
  · rintro ⟨hw, hu⟩ y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 M))).1 hy
    rw [FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 M))]
    refine mem_integers_of_valuation_le_one (R := 𝓞 M) (K := M) _ fun u ↦ ?_
    rw [map_mul, valuation_of_algebraMap]
    by_cases huw : u = w
    · subst huw
      calc u.valuation M x * u.intValuation y'
          ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) := by
            gcongr
            exact (u.intValuation_le_pow_iff_mem y' n).2 hy'
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    · simpa using mul_le_mul' (hu u huw) (u.intValuation_le_one y')

theorem exists_valuation_eq_exp (w : HeightOneSpectrum (𝓞 M)) (n : ℕ) :
    ∃ x : M, w.valuation M x = WithZero.exp (n : ℤ) ∧
      ∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M x ≤ 1 := by
  cases n with
  | zero => exact ⟨1, by simp, fun u _ ↦ by simp⟩
  | succ k =>
    by_contra H
    push Not at H
    have hle : ((w.asIdeal ^ (k + 1) : Ideal (𝓞 M)) :
        FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ≤
        ((w.asIdeal ^ k : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ := by
      intro x hx
      obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w (k + 1) x).1 hx
      refine (mem_inv_pow_iff w k x).2 ⟨?_, hxu⟩
      have hne : w.valuation M x ≠ WithZero.exp ((k + 1 : ℕ) : ℤ) := by
        intro heq
        obtain ⟨u, hu, hlt⟩ := H x heq
        exact absurd (hxu u hu) (not_le.2 hlt)
      have hlt : w.valuation M x < WithZero.exp (k : ℤ) * WithZero.exp 1 := by
        rw [← WithZero.exp_add]
        have := lt_of_le_of_ne hxw hne
        push_cast at this
        exact this
      exact (WithZero.lt_mul_exp_iff_le (by simp)).1 hlt
    have hge : ((w.asIdeal ^ k : Ideal (𝓞 M)) :
        FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ≤
        ((w.asIdeal ^ (k + 1) : Ideal (𝓞 M)) :
          FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ := by
      intro x hx
      obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w k x).1 hx
      refine (mem_inv_pow_iff w (k + 1) x).2 ⟨hxw.trans ?_, hxu⟩
      rw [WithZero.exp_le_exp]
      push_cast
      omega
    have heq := inv_inj.1 (le_antisymm hle hge)
    rw [FractionalIdeal.coeIdeal_inj] at heq
    exact (Ideal.pow_succ_lt_pow w.ne_bot k).ne heq

end Global

section Comparison

open SemiLocal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem valued_trace_le_one_of_valuation_le_one (v : HeightOneSpectrum (𝓞 K))
    (u : PlacesOver M v) {x : M} (hx : u.1.valuation M x ≤ 1) :
    Valued.v (Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
      (algebraMap M (u.1.adicCompletion M) x)) ≤ 1 := by
  refine (forall_valued_trace_le_one_iff v u.1 0).2 (Nat.zero_le _) _ ?_
  rw [valued_algebraMap_field, Nat.cast_zero, WithZero.exp_zero]
  exact hx

theorem trace_mem_range_of_forall (x : M)
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : PlacesOver M v),
      Valued.v (Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
        (algebraMap M (u.1.adicCompletion M) x)) ≤ 1) :
    Algebra.trace K M x ∈ (algebraMap (𝓞 K) K).range := by
  refine mem_integers_of_valuation_le_one (R := 𝓞 K) (K := K) _ fun v ↦ ?_
  rw [← valued_algebraMap_field, algebraMap_trace_eq_sum]
  exact Valuation.map_sum_le _ fun u _ ↦ h v u

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]

theorem differentIdeal_le_pow_of_le_differentExponent {n : ℕ}
    (hn : n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M)) :
    differentIdeal (𝓞 K) (𝓞 M) ≤ w.asIdeal ^ n := by
  have hI : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ w.ne_bot
  rw [differentialIdeal_le_iff (K := K) (L := M) hI, Submodule.map_le_iff_le_comap]
  intro x hx
  obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w n x).1 hx
  rw [Submodule.mem_comap]
  have hloc : ∀ (v' : HeightOneSpectrum (𝓞 K)) (u : PlacesOver M v'),
      Valued.v (Algebra.trace (v'.adicCompletion K) (u.1.adicCompletion M)
        (algebraMap M (u.1.adicCompletion M) x)) ≤ 1 := by
    intro v' u
    by_cases hu : u.1 = w
    · obtain ⟨u1, hu1⟩ := u
      simp only at hu
      subst hu
      have hv : v' = v := HeightOneSpectrum.ext
        ((Ideal.over_def u1.asIdeal v'.asIdeal).trans (Ideal.over_def u1.asIdeal v.asIdeal).symm)
      subst hv
      refine (forall_valued_trace_le_one_iff v' u1 n).2 hn _ ?_
      rw [valued_algebraMap_field]
      exact hxw
    · exact valued_trace_le_one_of_valuation_le_one v' u (hxu u.1 hu)
  obtain ⟨a, ha⟩ := trace_mem_range_of_forall (K := K) x hloc
  exact Submodule.mem_one.2 ⟨a, ha⟩

theorem le_differentExponent_of_differentIdeal_le_pow {n : ℕ}
    (h : differentIdeal (𝓞 K) (𝓞 M) ≤ w.asIdeal ^ n) :
    n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  classical
  have hI : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ w.ne_bot
  rw [differentialIdeal_le_iff (K := K) (L := M) hI, Submodule.map_le_iff_le_comap] at h
  let w0 : PlacesOver M v := ⟨w, inferInstance⟩

  have hX : ∀ X : M, w.valuation M X ≤ WithZero.exp (n : ℤ) →
      (∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M X ≤ 1) →
      Valued.v (Algebra.trace (v.adicCompletion K) (w.adicCompletion M)
        (algebraMap M (w.adicCompletion M) X)) ≤ 1 := by
    intro X hXw hXu
    obtain ⟨a, ha⟩ := Submodule.mem_one.1
      (Submodule.mem_comap.1 (h ((mem_inv_pow_iff w n X).2 ⟨hXw, hXu⟩)))
    have ha' : algebraMap (𝓞 K) K a = Algebra.trace K M X := ha
    have htot : Valued.v (algebraMap K (v.adicCompletion K) (Algebra.trace K M X)) ≤ 1 := by
      rw [← ha', ← IsScalarTower.algebraMap_apply]
      exact valued_algebraMap_int_le_one v a
    rw [algebraMap_trace_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ w0)] at htot
    have hrest : Valued.v (∑ u ∈ Finset.univ.erase w0,
        Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
          (algebraMap M (u.1.adicCompletion M) X)) ≤ 1 :=
      Valuation.map_sum_le _ fun u hu ↦ valued_trace_le_one_of_valuation_le_one v u
        (hXu u.1 fun he ↦ Finset.ne_of_mem_erase hu (Subtype.ext he))
    have hsplit : Algebra.trace (v.adicCompletion K) (w.adicCompletion M)
        (algebraMap M (w.adicCompletion M) X) =
        (Algebra.trace (v.adicCompletion K) (w0.1.adicCompletion M)
          (algebraMap M (w0.1.adicCompletion M) X) + ∑ u ∈ Finset.univ.erase w0,
            Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
              (algebraMap M (u.1.adicCompletion M) X)) - ∑ u ∈ Finset.univ.erase w0,
            Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
              (algebraMap M (u.1.adicCompletion M) X) := by
      rw [add_sub_cancel_right]
    rw [hsplit]
    exact (Valuation.map_sub _ _ _).trans (max_le htot hrest)
  rw [← forall_valued_trace_le_one_iff v w n]
  intro y hy
  obtain ⟨x0, hx0w, hx0u⟩ := exists_valuation_eq_exp w n
  set X0 := algebraMap M (w.adicCompletion M) x0 with hX0def
  have hX0 : Valued.v X0 = WithZero.exp (n : ℤ) := by
    rw [hX0def, valued_algebraMap_field]
    exact hx0w
  have hX00 : X0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hX0
    exact WithZero.zero_ne_coe hX0
  set z := X0⁻¹ * y with hzdef
  have hz : Valued.v z ≤ 1 := by
    rw [hzdef, map_mul, map_inv₀, hX0]
    calc (WithZero.exp (n : ℤ))⁻¹ * Valued.v y
        ≤ (WithZero.exp (n : ℤ))⁻¹ * WithZero.exp (n : ℤ) := by gcongr
      _ = 1 := inv_mul_cancel₀ (by simp)
  have hzmem : z ∈ (w.adicCompletionIntegers M : Set (w.adicCompletion M)) := hz
  have hopen : IsOpen ((fun s ↦ X0 * (z - s)) ⁻¹'
      ((Valued.v : Valuation (w.adicCompletion M) ℤᵐ⁰).integer : Set (w.adicCompletion M))) :=
    (Valued.isOpen_integer (w.adicCompletion M)).preimage (continuous_const.mul (continuous_const.sub continuous_id))
  have hzU : z ∈ ((fun s ↦ X0 * (z - s)) ⁻¹'
      ((Valued.v : Valuation (w.adicCompletion M) ℤᵐ⁰).integer : Set (w.adicCompletion M))) := by
    simp
  obtain ⟨_, hs, b, rfl⟩ := mem_closure_iff.1
    (adicCompletionIntegers_subset_closure_ringOfIntegers w hzmem) _ hopen hzU
  have hs' : Valued.v (X0 * (z - algebraMap M (w.adicCompletion M) (algebraMap (𝓞 M) M b))) ≤ 1 :=
    hs
  have hb : ∀ u : HeightOneSpectrum (𝓞 M), u.valuation M (algebraMap (𝓞 M) M b) ≤ 1 :=
    fun u ↦ u.valuation_le_one b
  have key := hX (x0 * algebraMap (𝓞 M) M b)
    (by simpa [map_mul, hx0w] using mul_le_mul' (le_refl (WithZero.exp (n : ℤ))) (hb w))
    (fun u hu ↦ by simpa [map_mul] using mul_le_mul' (hx0u u hu) (hb u))
  have hy : y = X0 * (z - algebraMap M (w.adicCompletion M) (algebraMap (𝓞 M) M b)) +
      algebraMap M (w.adicCompletion M) (x0 * algebraMap (𝓞 M) M b) := by
    rw [map_mul, ← hX0def, hzdef, mul_sub, ← mul_assoc, mul_inv_cancel₀ hX00, one_mul,
      sub_add_cancel]
  rw [hy, map_add]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ key)
  refine (forall_valued_trace_le_one_iff v w 0).2 (Nat.zero_le _) _ ?_
  rw [Nat.cast_zero, WithZero.exp_zero]
  exact hs'

theorem multiplicity_differentIdeal :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) =
      differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [emultiplicity_eq_coe, Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  refine ⟨differentIdeal_le_pow_of_le_differentExponent v w le_rfl, fun h ↦ ?_⟩
  have := le_differentExponent_of_differentIdeal_le_pow v w h
  omega

end Comparison

section Main

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem multiplicity_differentIdeal_eq_differentExponent (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
    [iA : Algebra (v.adicCompletion K) (w.adicCompletion M)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)] :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) =
      differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  have h : iA = SemiLocal.algebraCompletion v w := Algebra.algebra_ext _ _ fun r ↦ by
    rw [algebraMap_adicCompletion_eq v w]
    rfl
  subst h
  exact multiplicity_differentIdeal v w

open SemiLocal in

theorem multiplicity_relDiscr_semiLocal (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (relDiscr K M) =
      ∑ w : PlacesOver M v, w.1.asIdeal.inertiaDeg (𝓞 K) *
        differentExponent (v.adicCompletion K) (w.1.adicCompletion M) := by
  rw [multiplicity_relDiscr_eq_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [multiplicity_differentIdeal_eq_differentExponent v w.1]

end Main

end GroundTheory.Global
