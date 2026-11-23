import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocC
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IofAdd
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v)

omit [CharZero Ω] in
private theorem iof_mem (x : Ω) : x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := Examples₂.LB.mem_placeJ j x

omit [CharZero Ω] in
private theorem iof_lt (x : Ω) : (placeJ j).valuation x < 1 ↔ ‖j x‖ < 1 :=
  Examples₂.LB.val_lt_one_iff (iof_mem j) x

omit [CharZero Ω] in
private theorem iof_le (x : Ω) : (placeJ j).valuation x ≤ 1 ↔ ‖j x‖ ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, iof_mem]

private theorem iof_add {x y : Om v} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.Qk7.iof_add hx hy

private theorem iof_pow {x y : Om v} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [e]
    refine iof_add ?_ ?_
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt ih
    · rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)).trans_lt h

variable [IsAlgClosure ℚ Ω]

private theorem iof_dense : DenseRange j :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  Examples₂.LB.denseRange_emb v j

private theorem iof_pw (σ : GQ v) (n : ℕ) :
    (∀ x : Om v, ‖x‖ ≤ 1 → ‖σ x - x ^ n‖ < 1) ↔
      ∀ y : Ω, (placeJ j).valuation y ≤ 1 → (placeJ j).valuation (iota j σ y - y ^ n) < 1 := by
  simp only [iof_le, iof_lt, map_sub, map_pow, iota_spec]
  refine ⟨fun h y hy => h _ hy, fun h x hx => ?_⟩
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1 (iof_dense j) x 1 one_pos
  rw [dist_eq_norm] at hy
  have hy' : ‖j y - x‖ < 1 := by rwa [norm_sub_rev]
  have hy1 : ‖j y‖ ≤ 1 := by
    have e : j y = (j y - x) + x := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy'.le hx)
  have e : σ x - x ^ n = σ (x - j y) + ((σ (j y) - j y ^ n) + (j y ^ n - x ^ n)) := by
    rw [map_sub]; ring
  rw [e]
  exact iof_add (by rwa [Examples₂.LB.norm_aut]) (iof_add (h y hy1) (iof_pow hy1 hx hy' n))

private theorem iof_dec (σ : GQ v) : iota j σ ∈ Dec (F := ℚ) (placeJ j) := by
  rw [mem_Dec]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← map_inv, iof_mem, iof_mem,
    iota_spec, Examples₂.LB.norm_aut]

private theorem iof_range : (iota j).range = Dec (F := ℚ) (placeJ j) := by
  ext g
  constructor
  · rintro ⟨σ, rfl⟩
    exact iof_dec j σ
  · intro hg
    obtain ⟨σ, hσ⟩ := Examples₂.LB.exists_ext (E := ℚ) (iof_mem j) g hg
    exact ⟨σ, AlgEquiv.ext fun x => j.injective (by rw [iota_spec, hσ])⟩

private theorem iof_inj : Function.Injective (iota j) := by
  intro σ τ h
  refine AlgEquiv.ext fun y => ?_
  have e : σ ∘ j = τ ∘ j := funext fun x => by
    show σ (j x) = τ (j x)
    rw [← iota_spec, ← iota_spec, h]
  exact congrFun ((iof_dense j).equalizer (Examples₂.LB.continuous_aut _) (Examples₂.LB.continuous_aut _) e) y

private theorem iof_cont : Continuous (iota j) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨M, hM, hMU⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω U).mp hU
  let b := Module.finBasis ℚ M
  let N : IntermediateField ℚ_[v] (Om v) :=
    IntermediateField.adjoin ℚ_[v] (Set.range fun i => j (b i : Ω))
  have hN : FiniteDimensional ℚ_[v] N :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((IntermediateField.fixingSubgroup_isOpen N).mem_nhds
    (show (1 : GQ v) ∈ N.fixingSubgroup from one_mem _)) fun σ hσ => hMU ?_
  have hb : ∀ i, iota j σ (b i : Ω) = (b i : Ω) := fun i => j.injective (by
    rw [iota_spec]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩))
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have e : (iota j σ).toLinearMap ∘ₗ M.val.toLinearMap = M.val.toLinearMap := b.ext hb
  exact LinearMap.congr_fun e ⟨x, hx⟩

private theorem iof_ine (σ : GQ v) : iota j σ ∈ Ine (F := ℚ) (placeJ j) ↔ σ ∈ Iq v := by
  have h := iof_pw j σ 1
  simp only [pow_one] at h
  rw [(iqBasic v).2.2.1 σ, h]
  exact ⟨fun hg => hg.2, fun hg => ⟨iof_dec j σ, hg⟩⟩

private theorem iof_cyc (l : ℕ) [Fact l.Prime] (σ : GQ v) :
    cycZ ℚ Ω l (iota j σ) = UpperTheory.V.Loc.cyc v l σ := by
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.1 fun m => ?_)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have hζ' := hζ.map_of_injective j.injective
  have ha : iota j σ ζ = ζ ^ (((cycZ ℚ Ω l (iota j σ) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω (iota j σ)) ζ hζ.pow_eq_one
  have hb : σ (j ζ) = j ζ ^ (((UpperTheory.V.Loc.cyc v l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) σ) _ hζ'.pow_eq_one
  rw [← iota_spec, ha, map_pow] at hb
  exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)

omit [IsAlgClosure ℚ Ω] in
private theorem iof_place (w : HeightOneSpectrum (𝓞 ℚ)) :
    IsPlaceOver (placeJ j) w ↔ ((v : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  have h0 : (placeJ j).valuation ((v : ℕ) : Ω) < 1 := by
    rw [iof_lt, map_natCast]
    have h1 : ‖((v : ℕ) : PadicAlgCl v)‖ = ‖((v : ℕ) : ℚ_[v])‖ := by
      rw [← PadicAlgCl.norm_extends, map_natCast]
    rw [h1]
    exact Padic.norm_p_lt_one
  constructor
  · intro h
    refine (h _).1 ?_
    simpa using h0
  · intro h
    have e : Examples₂.LB.vQ v = w := HeightOneSpectrum.ext
      ((Examples₂.LB.vQ v).isMaximal.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h))
    rw [← e]
    exact Examples₂.LB.isPlaceOver_vQ _ h0

end SlopeTestRemainingChoices

theorem UpperTheory.V.Loc.iotaFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v), IsEmbedding (iota j) ∧ (iota j).range = Dec (F := ℚ) (placeJ j) ∧ (Ine (F := ℚ) (placeJ j)).comap (iota j) = Iq v ∧ (Iq v).map (iota j) = Ine (F := ℚ) (placeJ j) ∧ (∀ (l : ℕ) [Fact l.Prime], (cycZ ℚ Ω l).comp (iota j) = UpperTheory.V.Loc.cyc v l) ∧ (∀ w : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver (placeJ j) w ↔ ((v : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) ∧ ∀ σ : GQ v, UpperTheory.V.Loc.IsFrob σ ↔ Formalism.ConjugateSelfDual.IsFrob (F := ℚ) (placeJ j) v (iota j σ) := by
  intro Ω _ _ _ v _ j
  haveI : IsGalois ℚ_[v] (Om v) := {}
  refine ⟨((iof_cont j).isClosedEmbedding (iof_inj j)).isEmbedding, iof_range j, Subgroup.ext (iof_ine j), ?_,
    fun l _ => MonoidHom.ext (iof_cyc j l), iof_place j, fun σ => ?_⟩
  · ext g
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (iof_ine j σ).2 hσ
    · intro hg
      have h1 : g ∈ (iota j).range := by
        rw [iof_range]
        exact hg.1
      obtain ⟨σ, rfl⟩ := h1
      exact ⟨σ, (iof_ine j σ).1 hg, rfl⟩
  · exact (iof_pw j σ v).trans ⟨fun hg => ⟨iof_dec j σ, hg⟩, fun hg => hg.2⟩
