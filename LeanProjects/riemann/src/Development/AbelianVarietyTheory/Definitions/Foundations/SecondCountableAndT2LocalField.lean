import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise

noncomputable section
namespace GlobalTheory.SplitWeil.Model

theorem padic_lt (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]) :
    valuation ℚ_[p] x < valuation ℚ_[p] y ↔ ‖x‖ < ‖y‖ := by
  rw [(ValuativeRel.isEquiv (valuation ℚ_[p]) (Padic.mulValuation (p := p))).lt_iff_lt]
  by_cases hx : x = 0 <;> by_cases hy : y = 0
  · simp [hx, hy]
  · simp [hx, hy, zero_lt_iff]
  · simp [hx, hy]
  · have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
      zpow_lt_zpow_iff_right₀ hp]
    simp [Padic.mulValuation, hx, hy, inv_lt_inv₀]

theorem padic_valTop (p : ℕ) [Fact p.Prime] : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_zero fun s => ?_
  rw [Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hs⟩
    obtain ⟨y, hy0, hy⟩ := NormedField.exists_norm_lt ℚ_[p] hε
    have hy' : y ≠ 0 := norm_pos_iff.1 hy0
    refine ⟨Units.mk0 (valuation ℚ_[p] y) (by simpa using hy'), fun z hz => hs ?_⟩
    have : ‖z‖ < ‖y‖ := (padic_lt p z y).1 hz
    simpa using this.trans hy
  · rintro ⟨γ, hγ⟩
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero ℚ_[p])
    have hy' : y ≠ 0 := by rintro rfl; exact γ.ne_zero (by simpa using hy.symm)
    refine ⟨‖y‖, norm_pos_iff.2 hy', fun z hz => hγ ?_⟩
    show valuation ℚ_[p] z < γ
    rw [← hy, padic_lt]; simpa using hz

theorem padic_localField (p : ℕ) [Fact p.Prime] : IsNonarchimedeanLocalField ℚ_[p] :=
  { padic_valTop p with }

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountable_and_t2_local_field : SecondCountableTopology k ∧ T2Space k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem nabs_pos (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact_mod_cast distribHaarChar_pos

theorem nabs_mul (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by
  simp [nabs]

theorem nabs_one : nabs k 1 = 1 := by simp [nabs]

theorem om_one {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  funext x; simp [om, nabs_one]

theorem om_mul {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ) := by
  funext x
  simp only [om, map_mul, nabs_mul, Real.mul_rpow (nabs_pos _).le (nabs_pos _).le,
    _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Complex.ofReal_mul]
  ring

theorem not_hasConductor_one (c : kˣ) : ¬ HasConductor (1 : AddChar k Circle) c := by
  intro h
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have := (h (c / r)).1 (fun y _ => rfl)
  have hc : valuation k (c : k) ≠ 0 := by simp
  have hr' : valuation k r ≠ 0 := by simpa using hr
  rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 hr')] at this
  have h2 : valuation k (c : k) * valuation k r < valuation k (c : k) * 1 :=
    mul_lt_mul_of_pos_left hr1 (zero_lt_iff.2 hc)
  rw [mul_one] at h2
  exact absurd this (not_le.2 h2)

def ratCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

theorem ratCircle_eq_zero (x : AddCircle (1 : ℚ)) (h : ratCircle x = 0) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    have h' : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h'
    refine (AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this : (n : ℚ) = q)

theorem exists_hasConductor : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)⁻¹
  have ht1 : 1 < valuation k t := by
    rw [ht]; exact uniformizer_inv_le_iff.1 le_rfl
  let O : AddSubgroup k := (𝒪[k]).toAddSubgroup
  have hne : (QuotientAddGroup.mk t : k ⧸ O) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact not_le.2 ht1
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let c' : (k ⧸ O) →+ AddCircle (1 : ℚ) := c
  let f : k →+ AddCircle (1 : ℝ) := ratCircle.comp (c'.comp (QuotientAddGroup.mk' O))
  refine ⟨(AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom f, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩⟩
  · by_contra hx
    have hx' : 1 < valuation k x := by simpa using hx
    have h1 := h t (ht ▸ uniformizer_inv_le_iff.2 hx')
    have h2 : AddCircle.toCircle (f t) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h1
    exact hc (ratCircle_eq_zero _ (AddCircle.injective_toCircle one_ne_zero h2))
  · have hy' : (QuotientAddGroup.mk y : k ⧸ O) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact hy.trans (by simpa using h)
    show AddCircle.toCircle (ratCircle (c' (QuotientAddGroup.mk y))) = 1
    rw [hy']; simp

theorem KOne_le_KO (n : Type*) [Fintype n] [DecidableEq n] : KOne k n ≤ KO k n :=
  Subgroup.map_le_range _ _

theorem IsUnram.isTame {μ : kˣ →* ℂˣ} (h : IsUnram μ) : IsTame μ := fun x hx =>
  h x (by simpa using (valuation k).map_one_add_of_lt hx)

theorem isOpen_int : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer

theorem isCompact_int : IsCompact (𝒪[k] : Set k) :=
  IsNonarchimedeanLocalField.isCompact_closedBall k 1

variable [MeasurableSpace k] [BorelSpace k]

theorem exists_isUnitVol : ∃ ν : Measure k, IsUnitVol ν := by
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨(𝒪[k] : Set k), isCompact_int⟩, by
    rw [show interior ((⟨(𝒪[k] : Set k), isCompact_int⟩ : TopologicalSpace.Compacts k).carrier) =
      (𝒪[k] : Set k) from isOpen_int.interior_eq]
    exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩

theorem nabs_vol (ν : Measure k) (h : IsUnitVol ν) (x : kˣ) :
    ν (x • (𝒪[k] : Set k)) = ENNReal.ofReal (nabs k x) := by
  have := h.1
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  rw [← distribHaarChar_mul ν x, h.2]; simp [nabs]

theorem nabs_le_one (x : kˣ) (hx : valuation k (x : k) ≤ 1) : nabs k x ≤ 1 := by
  obtain ⟨ν, h⟩ := exists_isUnitVol (k := k)
  have : ν (x • (𝒪[k] : Set k)) ≤ ν (𝒪[k] : Set k) := by
    apply measure_mono
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (show (x : k) ∈ 𝒪[k] from hx) hy
  rw [nabs_vol ν h, h.2] at this
  exact ENNReal.ofReal_le_one.1 this

theorem volM_int (ν : Measure k) (h : IsUnitVol ν) (m n : Type*) [Fintype m] [Fintype n] :
    volM ν m n {x | ∀ i j, x i j ∈ (𝒪[k] : Set k)} = 1 := by
  have := h.1
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have : {x : Matrix m n k | ∀ i j, x i j ∈ (𝒪[k] : Set k)} =
      (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => (𝒪[k] : Set k) : Set (m → n → k)) :=
    Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
  rw [this]
  erw [Measure.pi_pi]
  simp [Measure.pi_pi, h.2]

theorem measurableEmbedding_val (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (fun g : GL n k => g.val) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  refine MeasurableEmbedding.iff_comap_eq.2 ⟨Units.val_injective, rfl, ?_⟩
  have hB : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    rfl
  rw [this]
  exact (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).measurableSet

omit [MeasurableSpace k] [BorelSpace k] in
theorem indicator_mem_SB : (𝒪[k] : Set k).indicator (fun _ => (1 : ℂ)) ∈ SB k := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have hcl : IsClopen (𝒪[k] : Set k) := ⟨isCompact_int.isClosed, isOpen_int⟩
  refine ⟨?_, HasCompactSupport.intro isCompact_int fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const k (1 : ℂ)) hcl).isLocallyConstant

omit [MeasurableSpace k] [BorelSpace k] in
theorem noncompact : NoncompactSpace k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedSpace.noncompactSpace k k

theorem not_isSelfDual_one (ν : Measure k) : ¬ IsSelfDual (1 : AddChar k Circle) ν := by
  rintro ⟨h1, h2⟩
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have := noncompact (k := k)
  have h := h2 _ indicator_mem_SB
  simp [Measure.real, measure_univ_of_isAddLeftInvariant ν, Set.indicator_of_mem (zero_mem 𝒪[k] : (0 : k) ∈ (𝒪[k] : Set k))] at h

omit [MeasurableSpace k] [BorelSpace k] in

theorem om_mem_SB {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    om μ g h Φ ∈ SB (Matrix b a k) := by
  let e : Matrix b a k ≃ₜ Matrix b a k :=
    { toFun := fun x => (h⁻¹ : GL b k).val * x * g.val
      invFun := fun x => h.val * x * (g⁻¹ : GL a k).val
      left_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  have h1 : (Φ ∘ e) ∈ SB (Matrix b a k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  exact (SB (Matrix b a k)).smul_mem _ h1

end GlobalTheory.SplitWeil.Model
