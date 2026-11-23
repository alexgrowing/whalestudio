import Mathlib
import GroundTheory.GlobalFields.CompletionAtPlace

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel

open scoped WithZero

namespace GroundTheory.Global

section Density

variable {L : Type*} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

theorem adicCompletionIntegers_subset_closure_ringOfIntegers :
    (w.adicCompletionIntegers L : Set (w.adicCompletion L)) ⊆
      closure (Set.range fun r : 𝓞 L ↦ algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have h1 : {y : w.adicCompletion L | Valued.v.restrict (y - x) < γ.1} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨γ, subset_rfl⟩
  have h2 : {y : w.adicCompletion L | Valued.v.restrict (y - x) <
      ((1 : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
        Valuation (w.adicCompletion L) ℤᵐ⁰)))ˣ) : _)} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨1, subset_rfl⟩
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 L) (K := L) w).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding] at hk1 hk2
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := by simp [hc]
  have hx1 : Valued.v x ≤ 1 := hx
  have hkv : w.valuation L k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation' w k]
    have : (k : w.adicCompletion L) = (algebraMap L (w.adicCompletion L) k - x) + x := by
      rw [sub_add_cancel]; rfl
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le hk2.le hx1)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer w hkv (Units.mk0 c hc0)
  refine ⟨_, hγ ?_, r, rfl⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  have hr' : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) -
      algebraMap L (w.adicCompletion L) k) < c := by
    rw [← map_sub]
    exact (valuedAdicCompletion_eq_valuation' w _).trans_lt hr
  have : algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) - x =
      (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) -
        algebraMap L (w.adicCompletion L) k) + (algebraMap L (w.adicCompletion L) k - x) := by
    ring
  rw [this]
  exact Valuation.map_add_lt _ hr' hk1

end Density

section IntegralClosure

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem mem_integer_of_isIntegral {x : w.adicCompletion L}
    (hx : IsIntegral 𝒪[v.adicCompletion K] x) : x ∈ 𝒪[w.adicCompletion L] :=
  (Valuation.integer.integers (valuation (w.adicCompletion L))).mem_of_integral
    (hx.tower_top (A := 𝒪[w.adicCompletion L]))

omit [Algebra K L] [w.asIdeal.LiesOver v.asIdeal]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in

theorem isIntegral_algebraMap_ringOfIntegers (r : 𝓞 L) :
    IsIntegral 𝒪[v.adicCompletion K]
      (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) := by
  obtain ⟨p, hp, hroot⟩ := RingOfIntegers.isIntegral_coe r
  refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, show (algebraMap 𝒪[v.adicCompletion K] (w.adicCompletion L)).comp
      (Int.castRingHom _) = (algebraMap L (w.adicCompletion L)).comp (algebraMap ℤ L) from
      RingHom.ext_int _ _, ← Polynomial.hom_eval₂]
  exact (congrArg (algebraMap L (w.adicCompletion L)) hroot).trans (map_zero _)

omit [Algebra K L] [w.asIdeal.LiesOver v.asIdeal]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in

theorem continuousSMul_integer :
    ContinuousSMul 𝒪[v.adicCompletion K] (w.adicCompletion L) := by
  refine continuousSMul_of_algebraMap _ _ ?_
  rw [IsScalarTower.algebraMap_eq 𝒪[v.adicCompletion K] (v.adicCompletion K)]
  exact (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).comp
    continuous_subtype_val

theorem isClosed_integralClosure :
    IsClosed ((integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) :
      Set (w.adicCompletion L))) := by
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have : ContinuousSMul 𝒪[v.adicCompletion K] (w.adicCompletion L) :=
    continuousSMul_integer v w
  have hfin : Module.Finite 𝒪[v.adicCompletion K]
      (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L)) :=
    IsIntegralClosure.finite 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' 𝒪[v.adicCompletion K]
    (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L))
  let g := (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L)).val.toLinearMap ∘ₗ f
  have hg : Continuous g := LinearMap.continuous_on_pi g
  have : ((integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) :
      Set (w.adicCompletion L))) = Set.range g := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := hf ⟨y, hy⟩
      exact ⟨c, by simp [g, hc]⟩
    · rintro ⟨c, rfl⟩
      exact (f c).2
  rw [this]
  exact (isCompact_range hg).isClosed

theorem isIntegral_of_mem_integer {x : w.adicCompletion L} (hx : x ∈ 𝒪[w.adicCompletion L]) :
    IsIntegral 𝒪[v.adicCompletion K] x := by
  have hx' : x ∈ w.adicCompletionIntegers L := (mem_valuationInteger_iff w x).1 hx
  have hsub : (Set.range fun r : 𝓞 L ↦
      algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) ⊆
      (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) : Set (w.adicCompletion L)) := by
    rintro _ ⟨r, rfl⟩
    exact isIntegral_algebraMap_ringOfIntegers v w r
  exact closure_minimal hsub (isClosed_integralClosure v w)
    (adicCompletionIntegers_subset_closure_ringOfIntegers w hx')

instance isIntegralClosure_integer :
    IsIntegralClosure 𝒪[w.adicCompletion L] 𝒪[v.adicCompletion K] (w.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := ⟨fun hx ↦ ⟨⟨x, mem_integer_of_isIntegral v w hx⟩, rfl⟩,
    fun ⟨y, hy⟩ ↦ hy ▸ isIntegral_of_mem_integer v w y.2⟩

end IntegralClosure

section MaximalIdeal

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem integers_valued :
    (Valued.v : Valuation (u.adicCompletion F) ℤᵐ⁰).Integers 𝒪[u.adicCompletion F] where
  hom_inj a b h := Subtype.ext h
  map_le_one y := by
    have h : (y : u.adicCompletion F) ∈ u.adicCompletionIntegers F :=
      (mem_valuationInteger_iff u (y : u.adicCompletion F)).1 y.2
    exact h
  exists_of_le_one x hx := ⟨⟨x, (mem_valuationInteger_iff u x).2 hx⟩, rfl⟩

theorem mem_maximalIdeal_iff_valued_lt_one (y : 𝒪[u.adicCompletion F]) :
    y ∈ 𝓂[u.adicCompletion F] ↔ Valued.v (y : u.adicCompletion F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (integers_valued u).isUnit_iff_valuation_eq_one]
  exact ⟨fun h ↦ lt_of_le_of_ne ((integers_valued u).map_le_one y) h, ne_of_lt⟩

theorem valued_of_irreducible_integer {ϖ : 𝒪[u.adicCompletion F]} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1) := by
  apply le_antisymm
  · have h := (mem_maximalIdeal_iff_valued_lt_one u ϖ).1 hϖ.not_isUnit
    have h' : Valued.v (ϖ : u.adicCompletion F) < WithZero.exp (-1) * WithZero.exp 1 := by
      rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    exact (WithZero.lt_mul_exp_iff_le (by simp)).1 h'
  · have hlt : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    obtain ⟨y, hy⟩ := valuedAdicCompletion_surjective F u (WithZero.exp (-1))
    have hy1 : Valued.v y ≤ 1 := by rw [hy]; exact hlt.le
    let y' : 𝒪[u.adicCompletion F] := ⟨y, (mem_valuationInteger_iff u y).2 hy1⟩
    have hy' : y' ∈ 𝓂[u.adicCompletion F] := by
      rw [mem_maximalIdeal_iff_valued_lt_one]
      change Valued.v y < 1
      rw [hy]; exact hlt
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hy'
    obtain ⟨c, hc⟩ := hy'
    rw [← hy, show y = ((c * ϖ : 𝒪[u.adicCompletion F]) : u.adicCompletion F) by rw [hc],
      Subring.coe_mul, map_mul]
    exact mul_le_of_le_one_left zero_le ((integers_valued u).map_le_one c)

theorem mem_maximalIdeal_pow_iff (y : 𝒪[u.adicCompletion F]) (n : ℕ) :
    y ∈ 𝓂[u.adicCompletion F] ^ n ↔ Valued.v (y : u.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[u.adicCompletion F]
  have h := (integers_valued u).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hϖ n
  rw [← SetLike.mem_coe, h, Set.mem_ofPred_eq]
  change Valued.v (y : u.adicCompletion F) ≤ Valued.v (ϖ : u.adicCompletion F) ^ n ↔ _
  rw [valued_of_irreducible_integer u hϖ, ← WithZero.exp_nsmul]
  simp

end MaximalIdeal

section Degree

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

instance charZero_adicCompletion {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) : CharZero (u.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (u.adicCompletion F)).injective

theorem isTorsionFree_integer_adicCompletion :
    Module.IsTorsionFree 𝒪[v.adicCompletion K] (w.adicCompletion L) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L)]
  exact (algebraMap (v.adicCompletion K) (w.adicCompletion L)).injective.comp
    Subtype.val_injective

theorem finite_integer : Module.Finite 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] :=
  IsIntegralClosure.finite 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _

theorem free_integer : Module.Free 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] :=
  have := isTorsionFree_integer_adicCompletion v w
  IsIntegralClosure.module_free 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _

theorem finrank_integer :
    Module.finrank 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) :=
  have := isTorsionFree_integer_adicCompletion v w
  IsIntegralClosure.rank 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _

theorem ramificationIdx_mul_inertiaDeg_integer :
    𝓂[w.adicCompletion L].ramificationIdx 𝒪[v.adicCompletion K] *
        𝓂[w.adicCompletion L].inertiaDeg 𝒪[v.adicCompletion K] =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have := finite_integer v w
  have := free_integer v w
  have hp0 : 𝓂[v.adicCompletion K] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hset := IsLocalRing.primesOver_eq 𝒪[w.adicCompletion L] hp0
  have hmem : 𝓂[w.adicCompletion L] ∈ 𝓂[v.adicCompletion K].primesOver 𝒪[w.adicCompletion L] := by
    rw [hset]; rfl
  let : Unique (𝓂[v.adicCompletion K].primesOver 𝒪[w.adicCompletion L]) :=
    { default := ⟨_, hmem⟩
      uniq := fun q ↦ Subtype.ext ((Set.ext_iff.1 hset q).1 q.2) }
  have h := Ideal.sum_ramification_inertia_eq_finrank 𝓂[v.adicCompletion K] 𝒪[w.adicCompletion L]
  rw [Fintype.sum_unique, finrank_integer] at h
  exact h

theorem ramificationIdx_integer :
    𝓂[w.adicCompletion L].ramificationIdx 𝒪[v.adicCompletion K] =
      w.asIdeal.ramificationIdx (𝓞 K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  have key : ∀ n : ℕ, Ideal.map (algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L])
      𝓂[v.adicCompletion K] ≤ 𝓂[w.adicCompletion L] ^ n ↔
        n ≤ v.asIdeal.ramificationIdx' w.asIdeal := by
    intro n
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
      mem_maximalIdeal_pow_iff, GroundTheory.LocalField.coe_algebraMap_integer,
      valued_algebraMap_adicCompletion', valued_of_irreducible_integer v hϖ,
      ← WithZero.exp_nsmul, WithZero.exp_le_exp]
    simp only [smul_neg, nsmul_eq_mul, mul_one, neg_le_neg_iff, Nat.cast_le]
  have h := Ideal.ramificationIdx'_spec ((key _).2 le_rfl)
    (fun h ↦ by simpa using (key _).1 h)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx 𝓂[v.adicCompletion K] 𝓂[w.adicCompletion L]
    (IsDiscreteValuationRing.not_a_field _), h,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]

end Degree

end GroundTheory.Global
