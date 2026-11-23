import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function Filter Topology

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem hausdorff_local_field : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

variable {K}

theorem valuation_lt_one_iff_topologically_nilpotent (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  constructor
  · intro hx
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
    intro γ _
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hx.le hm) hn
  · intro h
    have h1 := (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff.1 h 1 trivial
    obtain ⟨n, hn⟩ := (h1.and (eventually_ge_atTop 1)).exists
    obtain ⟨hn1, hn2⟩ := hn
    rw [Set.mem_ofPred_eq, map_pow, Units.val_one] at hn1
    by_contra hc
    exact absurd hn1 (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

theorem isClosed_valuation_integers : IsClosed (𝒪[K] : Set K) := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact Valued.isClosed_integer K

end

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

theorem exists_residue_char : ∃ p : ℕ, p.Prime ∧ valuation K (p : K) < 1 := by
  obtain ⟨p, hp⟩ := CharP.exists 𝓀[K]
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero 𝓀[K] p with h | h
    · exact h
    · subst h
      have := CharP.charP_to_charZero 𝓀[K]
      exact absurd (inferInstance : Finite 𝓀[K]) (not_finite_iff_infinite.2 inferInstance)
  refine ⟨p, hpp, ?_⟩
  have h0 : IsLocalRing.residue 𝒪[K] (p : 𝒪[K]) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ p
  rw [IsLocalRing.residue_eq_zero_iff] at h0
  have := (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation K) (x := (p : 𝒪[K]))).1 h0
  simpa using this

theorem finite_over_padic (p : ℕ) [Fact p.Prime] (f : ℚ_[p] →+* K) (hf : Continuous f) :
    letI := f.toAlgebra
    FiniteDimensional ℚ_[p] K := by
  let := f.toAlgebra
  have := hausdorff_local_field K
  have : ContinuousSMul ℚ_[p] K := continuousSMul_of_algebraMap _ _ hf
  exact FiniteDimensional.of_locallyCompactSpace ℚ_[p]

end

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  (p : ℕ) [Fact p.Prime]

theorem valuation_intCast_le_one_local_class_field (n : ℤ) : valuation K (n : K) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (intCast_mem 𝒪[K] n)

theorem rational_valuation_le_one (hp : valuation K (p : K) < 1) (q : ℚ) (hq : Rat.padicValuation p q ≤ 1) :
    valuation K (q : K) ≤ 1 := by
  rw [Rat.padicValuation_le_one_iff] at hq
  have hc : IsCoprime (p : ℤ) (q.den : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.2 (by
      rw [Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hq)
  obtain ⟨a, b, hab⟩ := hc
  have hden : 1 ≤ valuation K (q.den : K) := by
    by_contra hlt
    rw [not_le] at hlt
    have e : ((a : K) * (p : K) + (b : K) * (q.den : K)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
    have h1 : valuation K ((a : K) * (p : K)) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_intCast_le_one_local_class_field a)) hp
    have h2 : valuation K ((b : K) * (q.den : K)) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_intCast_le_one_local_class_field b)) hlt
    have := (valuation K).map_add_lt h1 h2
    rw [e, map_one] at this
    exact lt_irrefl _ this
  rw [Rat.cast_def, map_div₀]
  have hpos : 0 < valuation K (q.den : K) := lt_of_lt_of_le zero_lt_one hden
  rw [div_le_one₀ hpos]
  exact (valuation_intCast_le_one_local_class_field q.num).trans hden

noncomputable def transportRatHom (K : Type) [Field K] [CharZero K] : WithVal (Rat.padicValuation p) →+* K :=
  (algebraMap ℚ K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

theorem transportRatHom_apply (x : WithVal (Rat.padicValuation p)) :
    transportRatHom p K x = ((WithVal.equiv (Rat.padicValuation p) x : ℚ) : K) := rfl

theorem rational_valuation_le_pow (hp : valuation K (p : K) < 1) (q : ℚ) (n : ℕ)
    (hq : Rat.padicValuation p q < Rat.padicValuation p ((p : ℚ) ^ n)) :
    valuation K (q : K) ≤ valuation K (p : K) ^ n := by
  have hp0 : ((p : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hpv : Rat.padicValuation p ((p : ℚ) ^ n) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact hp0
  have h1 : Rat.padicValuation p (q / (p : ℚ) ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ (zero_lt_iff.2 hpv)).2 hq |>.le
  have h2 := rational_valuation_le_one (K := K) p hp _ h1
  have hpF : ((p : K) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hvF : valuation K ((p : K) ^ n) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hpF
  push_cast at h2
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hvF), map_pow] at h2
  exact h2

theorem continuous_rational_hom_of_valuation (hp : valuation K (p : K) < 1) : Continuous (transportRatHom p K) := by
  refine continuous_of_continuousAt_zero (transportRatHom p K) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hp γ
  let y : WithVal (Rat.padicValuation p) := WithVal.toVal _ ((p : ℚ) ^ n)
  have hy0 : y ≠ 0 := by
    simp only [y, ne_eq, WithVal.toVal_eq_zero]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hU := Valued.isOpen_ball (WithVal (Rat.padicValuation p)) (Valued.v.restrict y)
  have h0 : (0 : WithVal (Rat.padicValuation p)) ∈ {x | Valued.v.restrict x < Valued.v.restrict y} := by
    simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff, map_zero]
    exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
  rw [Filter.mem_map]
  filter_upwards [hU.mem_nhds h0] with x hx
  show transportRatHom p K x ∈ s
  simp only [Valuation.restrict_lt_iff] at hx
  apply hγ
  rw [Set.mem_ofPred_eq, transportRatHom_apply]
  exact lt_of_le_of_lt (rational_valuation_le_pow p hp _ n hx) hn

theorem exists_continuous_padic_hom (hp : valuation K (p : K) < 1) : ∃ f : ℚ_[p] →+* K, Continuous f := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  refine ⟨(UniformSpace.Completion.extensionHom (transportRatHom p K) (continuous_rational_hom_of_valuation p hp)).comp
    (Padic.withValRingEquiv (p := p)).symm.toRingHom, ?_⟩
  exact UniformSpace.Completion.continuous_extension.comp (Padic.withValUniformEquiv (p := p)).symm.continuous

end

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {p : ℕ} [Fact p.Prime]

theorem padic_hom_valuation_lt_one (f : ℚ_[p] →+* K) (hf : Continuous f) (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    valuation K (f x) < 1 := by
  rw [valuation_lt_one_iff_topologically_nilpotent]
  have h := (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one (x := x)).2 hx
  have h2 := (hf.tendsto 0).comp h
  rw [map_zero] at h2
  refine h2.congr fun n => ?_
  simp

theorem padic_hom_mem_integers_iff (f : ℚ_[p] →+* K) (hf : Continuous f) (x : ℚ_[p]) :
    f x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have hx0 : x ≠ 0 := by rintro rfl; simp at hc; linarith
    have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
    have h2 := padic_hom_valuation_lt_one f hf _ h1
    rw [Valuation.mem_integer_iff] at h
    have h3 : valuation K (f x * f x⁻¹) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h) h2
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one, map_one] at h3
    exact lt_irrefl _ h3
  · intro h
    have hcl : IsClosed {z : ℤ_[p] | f (z : ℚ_[p]) ∈ (𝒪[K] : Set K)} :=
      isClosed_valuation_integers.preimage (hf.comp continuous_subtype_val)
    have hall : ∀ z : ℤ_[p], f (z : ℚ_[p]) ∈ (𝒪[K] : Set K) := by
      intro z
      refine PadicInt.denseRange_intCast.induction_on (p := fun z : ℤ_[p] => f (z : ℚ_[p]) ∈ (𝒪[K] : Set K)) z hcl ?_
      intro n
      simp only [PadicInt.coe_intCast, map_intCast, SetLike.mem_coe]
      exact intCast_mem 𝒪[K] n
    exact hall ⟨x, h⟩

end

theorem mem_integers_iff_norm_of_homeomorph {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {L : Type} [NormedField L] (e : K ≃+* L) (he : IsHomeomorph e) (x : K) :
    x ∈ 𝒪[K] ↔ ‖e x‖ ≤ 1 := by
  have key : ∀ y : K, valuation K y < 1 ↔ ‖e y‖ < 1 := by
    intro y
    rw [valuation_lt_one_iff_topologically_nilpotent, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    have h0 : 𝓝 (0 : K) = comap e (𝓝 0) := by
      rw [← map_zero e]; exact he.isInducing.nhds_eq_comap 0
    rw [h0, tendsto_comap_iff]
    refine tendsto_congr fun n => ?_
    simp
  rw [Valuation.mem_integer_iff]
  by_cases hx : x = 0
  · subst hx; simp
  have h := key x⁻¹
  rw [map_inv₀, map_inv₀, norm_inv] at h
  have hv : 0 < valuation K x := zero_lt_iff.2 (by simpa using hx)
  have hn : 0 < ‖e x‖ := by rw [norm_pos_iff]; simpa using hx
  rw [inv_lt_one₀ hv, inv_lt_one₀ hn] at h
  rw [← not_lt, ← not_lt, h]

theorem exists_model_of_algebra (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [ContinuousSMul ℚ_[p] K] :
    ∃ m : Model K p, ∀ x : ℚ_[p], (m.e (algebraMap ℚ_[p] K x) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) x := by
  have := hausdorff_local_field K
  let φ : K →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift
  let e : K ≃ₐ[ℚ_[p]] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  have hfin : FiniteDimensional ℚ_[p] φ.fieldRange := Module.Finite.equiv e.toLinearEquiv
  let _ : Algebra K (PadicAlgCl p) := φ.toRingHom.toAlgebra
  have : IsScalarTower ℚ_[p] K (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : Algebra.IsAlgebraic K (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K
  have : IsAlgClosure K (PadicAlgCl p) := ⟨inferInstance, inferInstance⟩
  let E : AlgebraicClosure K ≃ₐ[K] PadicAlgCl p := IsAlgClosure.equiv K _ _
  have hhomeo : IsHomeomorph e.toRingEquiv :=
    (e.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph).isHomeomorph
  refine ⟨{ K' := φ.fieldRange, fin := hfin, e := e.toRingEquiv, E := E.toRingEquiv, comm := ?_, homeo := hhomeo, int := ?_ }, ?_⟩
  · intro x
    exact E.commutes x
  · intro x
    exact mem_integers_iff_norm_of_homeomorph e.toRingEquiv hhomeo x
  · intro x
    exact φ.commutes x

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

theorem exists_padic_hom (p : ℕ) [Fact p.Prime] (hp : valuation K (p : K) < 1) :
    ∃ f : ℚ_[p] →+* K, Continuous f ∧ ∀ x, f x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  obtain ⟨f, hf⟩ := exists_continuous_padic_hom (K := K) p hp
  exact ⟨f, hf, padic_hom_mem_integers_iff f hf⟩

theorem exists_model : ∃ (p : ℕ) (_ : Fact p.Prime), Nonempty (Model K p) := by
  obtain ⟨p, hpp, hp⟩ := exists_residue_char K
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨f, hf, -⟩ := exists_padic_hom K p hp
  let _ := f.toAlgebra
  have : FiniteDimensional ℚ_[p] K := finite_over_padic K p f hf
  have : ContinuousSMul ℚ_[p] K := continuousSMul_of_algebraMap _ _ hf
  obtain ⟨m, -⟩ := exists_model_of_algebra p K
  exact ⟨p, inferInstance, ⟨m⟩⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
