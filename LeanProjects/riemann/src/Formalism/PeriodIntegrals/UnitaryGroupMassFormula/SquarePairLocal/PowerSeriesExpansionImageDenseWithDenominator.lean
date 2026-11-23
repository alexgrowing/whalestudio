import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SigKApply

noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

namespace PI.SqPairLocal.Mdl

open PI.SqPairLocal Formalism.BasicNotions.Examples₂

variable {E : Type} [Field E] [NumberField E] [StarRing E] (v : HeightOneSpectrum (𝓞 E))

theorem ball_sub (x : v.adicCompletion E) {s : Set (v.adicCompletion E)} (hs : s ∈ 𝓝 x) :
    ∃ K : ℕ, ∀ z : v.adicCompletion E, Valued.v (z - x) ≤ exp (-(K : ℤ)) → z ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have h0 : embedding γ.1 ≠ 0 := fun h =>
    γ.ne_zero (embedding_injective (h.trans (map_zero _).symm))
  obtain ⟨K, hK⟩ := wz_exists_nat_lt _ h0
  refine ⟨K, fun z hz => hγ ?_⟩
  show Valued.v.restrict (z - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hz hK

theorem exists_val_pow (K : ℕ) :
    ∃ π : E, v.valuation E π = exp (-(K : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer E
  refine ⟨π ^ K, ?_⟩
  rw [map_pow, hπ, ← WithZero.exp_nsmul]
  congr 1
  simp

theorem nhds_lt (x : v.adicCompletion E) (K : ℕ) :
    {z : v.adicCompletion E | Valued.v (z - x) < exp (-(K : ℤ))} ∈ 𝓝 x := by
  obtain ⟨π, hπ⟩ := exists_val_pow v K
  have hv : Valued.v (algebraMap E (v.adicCompletion E) π) = exp (-(K : ℤ)) := by
    rw [adicCompl_val_algebraMap, hπ]
  have hr : Valued.v.restrict (algebraMap E (v.adicCompletion E) π) ≠ 0 := by
    intro h
    have := congrArg embedding h
    rw [Valuation.embedding_restrict, hv, map_zero] at this
    exact exp_ne_zero this
  refine Valued.mem_nhds.2 ⟨Units.mk0 _ hr, fun z hz => ?_⟩
  have hz' : Valued.v.restrict (z - x) < Valued.v.restrict (algebraMap E (v.adicCompletion E) π) := hz
  rw [Valuation.restrict_lt_iff_lt_embedding, Valuation.embedding_restrict, hv] at hz'
  exact hz'

theorem powerSeries_expansion_image_dense_with_denominator (x : v.adicCompletion E) (hx : x ∈ v.adicCompletionIntegers E) (K : ℕ) :
    ∃ y : 𝓞 E, Valued.v (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) - x) <
      exp (-(K : ℤ)) := by
  obtain ⟨_, hz, ⟨a, rfl⟩⟩ := mem_closure_iff_nhds.1
    (denseRange_algebraMap (R := 𝓞 E) (K := E) (v := v) x) _ (nhds_lt v x K)
  have hz' : Valued.v (algebraMap E (v.adicCompletion E) a - x) < exp (-(K : ℤ)) := hz
  have hK1 : exp (-(K : ℤ)) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]; omega
  have hx1 : Valued.v x ≤ 1 := hx
  have ha : v.valuation E a ≤ 1 := by
    rw [← adicCompl_val_algebraMap]
    have e : algebraMap E (v.adicCompletion E) a = (algebraMap E (v.adicCompletion E) a - x) + x := by
      ring
    rw [e]
    exact Valuation.map_add_le _ (hz'.le.trans hK1) hx1
  obtain ⟨y, hy⟩ := exists_valuation_sub_lt_of_integer (K := E) v ha (Units.mk0 _ exp_ne_zero)
  refine ⟨y, ?_⟩
  have e2 : algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) - x =
      algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y - a) +
        (algebraMap E (v.adicCompletion E) a - x) := by
    rw [map_sub]; ring
  rw [e2]
  refine Valuation.map_add_lt _ ?_ hz'
  rw [adicCompl_val_algebraMap]
  exact lt_of_lt_of_eq hy (Units.val_mk0 _)

section Sig

variable (hv : v.asIdeal.comap (cj E) = v.asIdeal)
include hv

theorem sigK_int (y : 𝓞 E) :
    sigK v hv (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y)) =
      algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E (cj E y)) := by
  rw [sigK_alg v hv]; rfl

theorem alg_int_mem (y : 𝓞 E) :
    algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) ∈ v.adicCompletionIntegers E := by
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 E) E v y

theorem sigK_mem (x : v.adicCompletion E) (hx : x ∈ v.adicCompletionIntegers E) :
    sigK v hv x ∈ v.adicCompletionIntegers E := by
  have hT : {z : v.adicCompletion E | sigK v hv (x - z) ∈ v.adicCompletionIntegers E} ∈ 𝓝 x := by
    have hc : Continuous fun z : v.adicCompletion E => sigK v hv (x - z) :=
      (sigK_cont v hv).comp (continuous_const.sub continuous_id)
    have ho : IsOpen ((v.adicCompletionIntegers E : Set (v.adicCompletion E))) :=
      Valued.isOpen_valuationSubring _
    refine hc.continuousAt.preimage_mem_nhds (ho.mem_nhds ?_)
    rw [sub_self, map_zero]
    exact (v.adicCompletionIntegers E).zero_mem
  obtain ⟨K, hK⟩ := ball_sub v x hT
  obtain ⟨y, hy⟩ := powerSeries_expansion_image_dense_with_denominator v x hx K
  have h1 := hK _ hy.le
  have e : sigK v hv x = sigK v hv (x - algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y)) +
      algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E (cj E y)) := by
    rw [map_sub, sigK_int v hv]; ring
  rw [e]
  exact add_mem h1 (alg_int_mem v hv _)

end Sig

end PI.SqPairLocal.Mdl
