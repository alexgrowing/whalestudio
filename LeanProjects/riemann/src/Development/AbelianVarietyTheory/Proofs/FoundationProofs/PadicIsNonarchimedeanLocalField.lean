import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology

noncomputable section
namespace GlobalTheory.SplitWeil

section Padic
variable (p : ℕ) [Fact p.Prime]

theorem padic_valuation_lt_iff (x y : ℚ_[p]) :
    valuation ℚ_[p] x < valuation ℚ_[p] y ↔ ‖x‖ < ‖y‖ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [(isEquiv (valuation ℚ_[p]) Padic.mulValuation).lt_iff_lt]
  by_cases hy : y = 0
  · simp [hy]
  by_cases hx : x = 0
  · simp [hx, hy, zero_lt_iff]
  rw [Padic.norm_eq_zpow_log_mulValuation hx, Padic.norm_eq_zpow_log_mulValuation hy,
    zpow_lt_zpow_iff_right₀ hp, WithZero.log_lt_log (by simpa using hx) (by simpa using hy)]

instance padic_isValuativeTopology : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_zero fun s => ?_
  rw [Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hs⟩
    obtain ⟨y, hy0, hy⟩ := NormedField.exists_norm_lt ℚ_[p] hε
    refine ⟨Units.mk0 (valuation ℚ_[p] y) (by simpa using norm_pos_iff.mp hy0), fun z hz => hs ?_⟩
    rw [mem_ball_zero_iff]
    exact ((padic_valuation_lt_iff p z y).mp hz).trans hy
  · rintro ⟨γ, hs⟩
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero ℚ_[p])
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact γ.ne_zero (by simpa using hy.symm)
    refine ⟨‖y‖, norm_pos_iff.mpr hy0, fun z hz => hs ?_⟩
    rw [mem_ball_zero_iff] at hz
    show valuation ℚ_[p] z < γ
    rw [← hy]
    exact (padic_valuation_lt_iff p z y).mpr hz

instance padic_isNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where

end Padic

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountable : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

theorem t2Space : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

theorem isOpen_int : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer

theorem isCompact_int : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1

theorem nabs_mul (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by simp [nabs]

theorem nabs_one : nabs k 1 = 1 := by simp [nabs]

theorem nabs_pos (x : kˣ) : 0 < nabs k x := by
  simpa [nabs] using distribHaarChar_pos (A := k) (g := x)

variable {k}

def cball (s : kˣ) : Set k := {x | valuation k x ≤ valuation k (s : k)}

theorem cball_eq_smul (s : kˣ) : cball s = s • (𝒪[k] : Set k) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [cball, Set.mem_setOf_eq, SetLike.mem_coe, Valuation.mem_integer_iff, Units.smul_def,
    smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  rw [inv_mul_le_iff₀ (by simp [zero_lt_iff]), mul_one]

theorem isOpen_cball (s : kˣ) : IsOpen (cball s) := by
  rw [cball_eq_smul]; exact (isOpen_int k).smul s

theorem isCompact_cball (s : kˣ) : IsCompact (cball s) :=
  IsNonarchimedeanLocalField.isCompact_closedBall k _

theorem cball_mem_nhds (s : kˣ) : cball s ∈ 𝓝 (0 : k) :=
  (isOpen_cball s).mem_nhds (by simp [cball])

theorem exists_cball_subset {U : Set k} (hU : U ∈ 𝓝 (0 : k)) : ∃ s : kˣ, cball s ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  refine ⟨Units.mk0 (r * y) (mul_ne_zero hr0 hy0), fun z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k (r * y) := hz
  refine lt_of_le_of_lt hz' ?_
  rw [map_mul, hy]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

section Meas
variable [MeasurableSpace k] [BorelSpace k]

variable (k) in
theorem exists_isUnitVol : ∃ ν : Measure k, IsUnitVol ν := by
  let K : TopologicalSpace.PositiveCompacts k :=
    ⟨⟨𝒪[k], isCompact_int k⟩, by
      simp only [(isOpen_int k).interior_eq]
      exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩

theorem measure_cball (ν : Measure k) [ν.IsAddHaarMeasure] (s : kˣ) :
    ν (cball s) = distribHaarChar k s * ν (𝒪[k] : Set k) := by
  haveI := secondCountable k
  haveI := t2Space k
  rw [cball_eq_smul, distribHaarChar_mul]

theorem measureReal_cball (ν : Measure k) [ν.IsAddHaarMeasure] (s : kˣ) :
    ν.real (cball s) = nabs k s * ν.real (𝒪[k] : Set k) := by
  simp [Measure.real, measure_cball, nabs]

end Meas

theorem nabs_eq_one_of_valuation_eq_one {x : kˣ} (hx : valuation k (x : k) = 1) : nabs k x = 1 := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  have h := measureReal_cball ν x
  have : cball x = (𝒪[k] : Set k) := by
    ext y; simp [cball, hx, Valuation.mem_integer_iff]
  rw [this, Measure.real, h1] at h
  simpa using h.symm

theorem mem_cball_uniformiser {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {x : kˣ} (hx : (x : k) = ϖ) (y : 𝒪[k]) :
    (y : k) ∈ cball x ↔ y ∈ 𝓂[k] := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, cball, Set.mem_setOf_eq, hx]
  exact (Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k)))

theorem nabs_uniformiser {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {x : kˣ} (hx : (x : k) = ϖ) :
    nabs k x = (resCard k : ℝ)⁻¹ := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
  let S : 𝓀[k] → Set k := fun r => (fun z => -(l r : k) + z) ⁻¹' cball x
  have hS : ∀ (r : 𝓀[k]) (y : 𝒪[k]), (y : k) ∈ S r ↔ IsLocalRing.residue _ y = r := by
    intro r y
    have := mem_cball_uniformiser hϖ hx (-(l r) + y)
    rw [← IsLocalRing.residue_eq_zero_iff, map_add, map_neg, hl, neg_add_eq_zero, eq_comm] at this
    simpa [S] using this
  have hsub : ∀ r, S r ⊆ (𝒪[k] : Set k) := by
    intro r z hz
    have h2 : -(l r : k) + z ∈ 𝒪[k] := by
      have : valuation k (-(l r : k) + z) ≤ valuation k (x : k) := hz
      rw [hx] at this
      exact this.trans ((Valuation.mem_integer_iff _ _).mp ϖ.2)
    simpa using add_mem (l r).2 h2
  have hU : (𝒪[k] : Set k) = ⋃ r, S r := by
    refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion_subset hsub)
    exact Set.mem_iUnion.mpr ⟨_, (hS _ ⟨z, hz⟩).mpr rfl⟩
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro r r' hr
    refine Set.disjoint_left.mpr fun z hz hz' => hr ?_
    exact ((hS r ⟨z, hsub r hz⟩).mp hz).symm.trans ((hS r' ⟨z, hsub r hz⟩).mp hz')
  have hm : ∀ r, MeasurableSet (S r) := fun r =>
    ((isOpen_cball x).preimage (by fun_prop)).measurableSet
  have h2 : ν (𝒪[k] : Set k) = ∑' r, ν (S r) := by rw [hU, measure_iUnion hd hm]
  have h3 : ∀ r, ν (S r) = distribHaarChar k x := by
    intro r
    simp only [S]
    rw [measure_preimage_add, measure_cball, h1, mul_one]
  haveI := Fintype.ofFinite 𝓀[k]
  simp only [h3, h1, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  have h4 := congrArg ENNReal.toReal h2
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal] at h4
  rw [resCard, Nat.card_eq_fintype_card, nabs]
  exact eq_inv_of_mul_eq_one_right h4.symm

section Om
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)

theorem om_one (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  funext x
  simp [om, nabs_one]

theorem om_mul (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ) := by
  funext x
  simp only [om, map_mul, nabs_mul, Real.mul_rpow (nabs_pos k _).le (nabs_pos k _).le,
    _root_.mul_inv_rev, Units.val_mul, Complex.ofReal_mul, Matrix.mul_assoc]
  ring

def sideMul (g : GL a k) (h : GL b k) : Matrix b a k ≃ₜ Matrix b a k where
  toFun x := (h⁻¹ : GL b k).val * x * g.val
  invFun x := h.val * x * (g⁻¹ : GL a k).val
  left_inv x := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv x := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem om_mem_SB (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    om μ g h Φ ∈ SB (Matrix b a k) := by
  have h1 : Φ ∘ sideMul g h ∈ SB (Matrix b a k) :=
    ⟨hΦ.1.comp_continuous (sideMul g h).continuous, hΦ.2.comp_homeomorph _⟩
  exact (SB _).smul_mem _ h1

end Om

section Char

def ratCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

theorem ratCircle_eq_zero {x : AddCircle (1 : ℚ)} (h : ratCircle x = 0) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with | H r => ?_
  have h' : (((r : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h'
  refine (AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩
  rw [zsmul_eq_mul, mul_one] at hn ⊢
  exact_mod_cast hn

variable (k) in

theorem exists_hasConductor_one : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hlt : ∀ y : 𝒪[k], y ∈ 𝓂[k] ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hϖ1 : valuation k (ϖ : k) < 1 := (hlt ϖ).mp hϖ.not_isUnit
  let A := (𝒪[k]).toAddSubgroup
  have hne : (QuotientAddGroup.mk (ϖ : k)⁻¹ : k ⧸ A) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    have h' : valuation k (ϖ : k)⁻¹ ≤ 1 := (Valuation.mem_integer_iff _ _).mp h
    rw [map_inv₀, inv_le_one₀ (by simp [zero_lt_iff, h0])] at h'
    exact absurd hϖ1 (not_lt.mpr h')
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let χ : k →+ AddCircle (1 : ℝ) := ratCircle.comp (AddMonoidHom.comp c (QuotientAddGroup.mk' A))
  refine ⟨AddCircle.toCircle_addChar.compAddMonoidHom χ, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩⟩
  · by_contra hx
    rw [Units.val_one, map_one, not_le] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hxi : valuation k x⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
    have h1 := (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl
      ⟨x⁻¹, (Valuation.mem_integer_iff _ _).mpr hxi.le⟩).mpr ((hlt _).mpr hxi)
    have h2 : valuation k x⁻¹ ≤ valuation k (ϖ : k) := h1
    have h3 := h (ϖ : k)⁻¹ (by
      rw [map_inv₀] at h2 ⊢
      exact inv_le_of_inv_le₀ (by simp [zero_lt_iff, hx0]) h2)
    have h4 : AddCircle.toCircle (χ (ϖ : k)⁻¹) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h3
    exact hc (ratCircle_eq_zero (AddCircle.injective_toCircle one_ne_zero h4))
  · have hy' : (QuotientAddGroup.mk y : k ⧸ A) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact (Valuation.mem_integer_iff _ _).mpr (by simpa using hy.trans h)
    have : χ y = 0 := by
      show ratCircle (c (QuotientAddGroup.mk y)) = 0
      rw [hy', map_zero, map_zero]
    show AddCircle.toCircle (χ y) = 1
    rw [this, AddCircle.toCircle_zero]

variable {ψ : AddChar k Circle} {c : kˣ}

theorem HasConductor.eq_one (h : HasConductor ψ c) {y : k} (hy : y ∈ cball c) : ψ y = 1 :=
  (h c).mpr le_rfl y hy

theorem HasConductor.ne_one (h : HasConductor ψ c) : ψ ≠ 1 := by
  rintro rfl
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have h1 := (h (r⁻¹ * c)).mp fun y _ => by simp
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ (by simp [zero_lt_iff, hr0])] at h1
  exact absurd (mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1) (not_lt.mpr h1)

theorem HasConductor.isLocallyConstant (h : HasConductor ψ c) : IsLocallyConstant ψ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' cball c ∈ 𝓝 x :=
    ((isOpen_cball c).preimage (by fun_prop)).mem_nhds (by simp [cball])
  filter_upwards [this] with z hz
  have h1 := h.eq_one hz
  have h2 : z = x + (-x + z) := by ring
  rw [h2, AddChar.map_add_eq_mul, h1, mul_one]

theorem HasConductor.continuous (h : HasConductor ψ c) : Continuous ψ := h.isLocallyConstant.continuous

theorem HasConductor.exists_ne_one (h : HasConductor ψ c) (s : kˣ) {x : k} (hx : x ∉ cball (c * s⁻¹)) :
    ∃ t ∈ cball s, ψ (t * x) ≠ 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp [cball])
  by_contra hne
  push Not at hne
  apply hx
  have h1 := (h (s * x)).mp fun y hy => by
    have := hne (y * x⁻¹) (by
      rw [cball, Set.mem_setOf_eq, map_mul, map_inv₀, mul_inv_le_iff₀ (by simp [zero_lt_iff, hx0]), ← map_mul]
      exact hy)
    rwa [inv_mul_cancel_right₀ hx0] at this
  rw [cball, Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
    le_mul_inv_iff₀ (by simp [zero_lt_iff]), mul_comm, ← map_mul]
  exact h1

theorem add_mem_cball {s : kˣ} {x y : k} (hx : x ∈ cball s) (hy : y ∈ cball s) : x + y ∈ cball s := by
  rw [cball, Set.mem_setOf_eq] at *
  exact Valuation.map_add_le _ hx hy

theorem neg_mem_cball {s : kˣ} {x : k} (hx : x ∈ cball s) : -x ∈ cball s := by
  simpa [cball] using hx

theorem exists_cball_invariant {f : k → ℂ} (hf : f ∈ SB k) :
    ∃ s : kˣ, ∀ t ∈ cball s, ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : k), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : k × k => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · have := hs (neg_mem_cball ht) _ hx'
    rw [← this, add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem fourier_eq_zero (h : HasConductor ψ c) {s : kˣ} {f : k → ℂ}
    (hs : ∀ t ∈ cball s, ∀ x, f (x + t) = f x) {y : k} (hy : y ∉ cball (c * s⁻¹)) :
    ∫ x, f x * (ψ (x * y) : ℂ) ∂ν = 0 := by
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one s hy
  have h1 := integral_add_right_eq_self (μ := ν) (fun x => f x * (ψ (x * y) : ℂ)) t
  have h2 : ∀ x, f (x + t) * (ψ ((x + t) * y) : ℂ) = (ψ (t * y) : ℂ) * (f x * (ψ (x * y) : ℂ)) := by
    intro x
    rw [hs t ht, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp only [h2, integral_const_mul] at h1
  have h3 : (ψ (t * y) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
  refine (mul_eq_zero.mp ?_).resolve_left h3
  rw [sub_mul, h1, one_mul, sub_self]

theorem fourier_indicator (h : HasConductor ψ c) (s : kˣ) (x : k) :
    ∫ y, (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y * x) : ℂ) ∂ν =
      (cball s).indicator (fun _ => (ν.real (cball (c * s⁻¹)) : ℂ)) x := by
  by_cases hx : x ∈ cball s
  · rw [Set.indicator_of_mem hx]
    have : ∀ y, (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y * x) : ℂ) =
        (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y := by
      intro y
      by_cases hy : y ∈ cball (c * s⁻¹)
      · have h1 : y * x ∈ cball c := by
          have h2 : valuation k (y * x) ≤ valuation k (((c * s⁻¹ : kˣ) : k) * s) := by
            rw [map_mul, map_mul]
            exact mul_le_mul' hy hx
          rwa [← Units.val_mul, inv_mul_cancel_right] at h2
        rw [h.eq_one h1, Circle.coe_one, mul_one]
      · simp [Set.indicator_of_notMem hy]
    simp only [this]
    rw [integral_indicator_const _ (isOpen_cball _).measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    refine fourier_eq_zero ν h (s := c * s⁻¹) (fun t ht y => ?_) (by simpa using hx)
    by_cases hy : y ∈ cball (c * s⁻¹)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (add_mem_cball hy ht)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro h1
      exact hy (by simpa using add_mem_cball h1 (neg_mem_cball ht))

theorem fourier_inversion (h : HasConductor ψ c) {f : k → ℂ} (hf : f ∈ SB k) :
    ∫ y, (∫ x, f x * (ψ (x * y) : ℂ) ∂ν) ∂ν =
      ((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_cball_invariant hf
  set e : k → ℂ := (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) with he
  have h1 : ∀ y, ∫ x, f x * (ψ (x * y) : ℂ) ∂ν = ∫ x, f x * (e y * (ψ (y * x) : ℂ)) ∂ν := by
    intro y
    by_cases hy : y ∈ cball (c * s⁻¹)
    · simp [he, Set.indicator_of_mem hy, mul_comm y]
    · simp [he, Set.indicator_of_notMem hy, fourier_eq_zero ν h hs hy]
  have hei : Integrable e ν :=
    (integrable_indicator_iff (isOpen_cball _).measurableSet).mpr
      (integrableOn_const (isCompact_cball _).measure_lt_top.ne)
  have hfi : Integrable f ν := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hint : Integrable (Function.uncurry fun y x => f x * (e y * (ψ (y * x) : ℂ))) (ν.prod ν) := by
    have h2 := (hei.mul_prod hfi).mul_bdd (c := 1) (g := fun q : k × k => (ψ (q.1 * q.2) : ℂ))
      (Continuous.aestronglyMeasurable
        (continuous_subtype_val.comp (h.continuous.comp (by fun_prop))))
      (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry]
    ring
  simp only [h1]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul, he, fourier_indicator ν h s]
  have h3 : ∀ x, f x * (cball s).indicator (fun _ => (ν.real (cball (c * s⁻¹)) : ℂ)) x =
      (cball s).indicator (fun _ => (ν.real (cball (c * s⁻¹)) : ℂ) * f 0) x := by
    intro x
    by_cases hx : x ∈ cball s
    · have := hs x hx 0
      rw [zero_add] at this
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, this, mul_comm]
    · simp [Set.indicator_of_notMem hx]
  simp only [h3]
  rw [integral_indicator_const _ (isOpen_cball _).measurableSet, measureReal_cball, measureReal_cball,
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  rw [h4]; ring

omit [ν.IsAddHaarMeasure] in

theorem isSelfDual_of_isUnitVol (h : HasConductor ψ 1) (hν : IsUnitVol ν) : IsSelfDual ψ ν := by
  haveI := hν.1
  refine ⟨hν.1, fun f hf => ?_⟩
  rw [fourier_inversion ν h hf, Measure.real, hν.2, nabs_one]
  simp

end Char

end GlobalTheory.SplitWeil
