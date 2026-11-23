import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.UnramDict

section
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem t2Space_isNonarchimedeanLocalField_singleBlock : T2Space K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem exists_pow_lt_value {a γ : ValueGroupWithZero K} (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ m < γ := by
  have e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have : MulArchimedean (ValueGroupWithZero K) := .comap e.toMonoidHom e.strictMono
  exact exists_pow_lt₀ ha (Units.mk0 γ hγ)

variable {K}

theorem exists_value_eq_zpow {π : K} (h0 : valuation K π ≠ 0) (h1 : valuation K π < 1)
    (hmax : ∀ x : K, valuation K x < 1 → valuation K x ≤ valuation K π) {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation K x = valuation K π ^ m := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hb0 : e (valuation K π) ≠ 0 := by
    intro h
    exact h0 (e.injective (h.trans (map_zero e).symm))
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hey : e (valuation K y) = WithZero.exp (-1 : ℤ) := by rw [hy]; simp
  have hy1 : valuation K y < 1 := by
    rw [← e.strictMono.lt_iff_lt, hey, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hle : e (valuation K y) ≤ e (valuation K π) := e.strictMono.monotone (hmax y hy1)
  have hlt : e (valuation K π) < 1 := by simpa using e.strictMono h1
  have hb : e (valuation K π) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨b, hbe⟩ : ∃ b : ℤ, e (valuation K π) = WithZero.exp b := ⟨_, (WithZero.exp_log hb0).symm⟩
    rw [hbe] at hle hlt ⊢
    rw [hey, WithZero.exp_le_exp] at hle
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    congr 1
    omega
  have hx0 : e (valuation K x) ≠ 0 := by
    intro h
    exact (Valuation.ne_zero_iff _).2 hx (e.injective (h.trans (map_zero e).symm))
  refine ⟨-WithZero.log (e (valuation K x)), e.injective ?_⟩
  have hz : (WithZero.exp (-1 : ℤ)) ^ (-WithZero.log (e (valuation K x))) =
      e (valuation K x) := by
    rw [← WithZero.exp_zsmul]
    simpa using WithZero.exp_log hx0
  show e (valuation K x) = e (valuation K π ^ (-WithZero.log (e (valuation K x))))
  rw [map_zpow₀ e, hb, hz]

end

section Matrices

theorem mem_unitGL_iff {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ((h : Matrix (Fin n) (Fin n) (intO F)) i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact (((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2
  · rintro ⟨hA, hB⟩
    let f : intO F →+* F := (intO F).subtype
    let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hA i j⟩
    let B : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hB i j⟩
    have hinj : Function.Injective (f.mapMatrix (m := Fin n)) :=
      Matrix.map_injective Subtype.val_injective
    have hAf : f.mapMatrix A = (g : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hBf : f.mapMatrix B = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      ext i j; rfl
    have hAB : A * B = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.mul_inv g)
    have hBA : B * A = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.inv_mul g)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hAf⟩

end Matrices

section Extension

variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]

theorem value_algebraMap_le_iff [ValuativeExtension k E] (a b : k) :
    valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) ↔
      valuation k a ≤ valuation k b := by
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le,
    ValuativeExtension.vle_iff_vle]

theorem tendsto_pow_zero {x : E} (hx : valuation E x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E hx hγ
  filter_upwards [eventually_ge_atTop m] with n hn
  show valuation E (x ^ n) < γ
  rw [map_pow]
  exact (pow_le_pow_right_of_le_one' hx.le hn).trans_lt hm

theorem continuous_algebraMap_of_lt_one [ValuativeExtension k E] {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1) :
    Continuous (algebraMap k E) := by
  refine continuous_of_continuousAt_zero (algebraMap k E) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E h1 hγ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at h0
  have hmem : {a : k | valuation k a < valuation k (π ^ m)} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem (by simpa using pow_ne_zero m hπ0)
  filter_upwards [hmem] with a ha
  have h2 : valuation E (algebraMap k E a) < valuation E (algebraMap k E (π ^ m)) := by
    rw [← not_le, value_algebraMap_le_iff, not_le]
    exact ha
  show valuation E (algebraMap k E a) < γ
  refine h2.trans_le ?_
  rw [map_pow, map_pow]
  exact hm.le

theorem continuous_linearMap [FiniteDimensional k E] [ContinuousSMul k E] (f : E →ₗ[k] E) :
    Continuous f := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  haveI := t2Space_isNonarchimedeanLocalField_singleBlock E
  exact f.continuous_of_finiteDimensional

theorem value_lt_one_of_continuous (τ : E ≃ₐ[k] E) (hτ : Continuous τ) {x : E}
    (hx : valuation E x < 1) : valuation E (τ x) < 1 := by
  have ht : Tendsto (fun n : ℕ => τ (x ^ n)) atTop (𝓝 0) := by
    have h := (hτ.tendsto 0).comp (tendsto_pow_zero hx)
    rw [map_zero] at h
    exact h
  have hmem : {y : E | valuation E y < 1} ∈ 𝓝 (0 : E) :=
    (IsValuativeTopology.hasBasis_nhds_zero' E).mem_of_mem one_ne_zero
  obtain ⟨n, hn, hn0⟩ := ((ht.eventually hmem).and (eventually_gt_atTop 0)).exists
  by_contra hc
  have h1 : 1 ≤ valuation E (τ x) ^ n := one_le_pow₀ (not_lt.1 hc)
  have h2 : valuation E (τ (x ^ n)) < 1 := hn
  rw [map_pow, map_pow] at h2
  exact absurd h2 (not_lt.2 h1)

theorem value_le_one_of_continuous (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x ≤ 1) : valuation E (τ x) ≤ 1 := by
  by_contra h
  have h1 : 1 < valuation E (τ x) := not_le.1 h
  have hy0 : valuation E (τ x) ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : valuation E (τ x)⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  have h3 := value_lt_one_of_continuous τ.symm (hc _) h2
  rw [map_inv₀, AlgEquiv.symm_apply_apply, map_inv₀] at h3
  have hx0 : valuation E x ≠ 0 := by
    intro h0
    have : x = 0 := (Valuation.zero_iff _).1 h0
    simp [this] at hy0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hx0)).1 h3) (not_lt.2 hx)

theorem value_eq_one_of_continuous (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x = 1) : valuation E (τ x) = 1 := by
  refine le_antisymm (value_le_one_of_continuous hc τ hx.le) ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 : valuation E x⁻¹ ≤ 1 := by rw [map_inv₀, hx, inv_one]
  have h2 := value_le_one_of_continuous hc τ h1
  rw [map_inv₀, map_inv₀] at h2
  have hy0 : valuation E (τ x) ≠ 0 := by simpa using hx0
  exact (inv_le_one₀ (zero_lt_iff.2 hy0)).1 h2

theorem value_map_eq (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1)
    (hmax : ∀ x : E, valuation E x < 1 → valuation E x ≤ valuation E (algebraMap k E π))
    (τ : E ≃ₐ[k] E) (x : E) : valuation E (τ x) = valuation E x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm⟩ := exists_value_eq_zpow h0 h1 hmax hx
  set p := algebraMap k E π with hp
  have hy : valuation E (x * p ^ (-m)) = 1 := by
    rw [map_mul, map_zpow₀, hm, ← zpow_add₀ h0]
    simp
  have h2 := value_eq_one_of_continuous hc τ hy
  rw [map_mul, map_zpow₀ τ, hp, τ.commutes, ← hp, map_mul, map_zpow₀, zpow_neg,
    mul_inv_eq_one₀ (zpow_ne_zero _ h0)] at h2
  rw [h2, hm]

end Extension

theorem unramifiedDictionary_a : PositivityTheory.Rg.Tf.Loc.D0a := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ _
  obtain ⟨π, h1, hmax⟩ := hun
  have h0 : valuation E (algebraMap k E π) ≠ 0 := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation E)
    intro h
    have := hmax r hr1
    rw [h] at this
    exact hr0 ((Valuation.zero_iff _).1 (le_antisymm this zero_le'))
  have hcont := continuous_algebraMap_of_lt_one h0 h1
  haveI : ContinuousSMul k E := continuousSMul_of_algebraMap k E hcont
  have hc : ∀ τ : E ≃ₐ[k] E, Continuous τ := fun τ => continuous_linearMap τ.toLinearMap
  have hval := value_map_eq hc h0 h1 hmax
  have hint : ∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k := by
    intro a
    have := value_algebraMap_le_iff (E := E) a 1
    simpa [Valuation.mem_integer_iff] using this
  refine ⟨hval, hint, ?_, ?_, hcont, ?_⟩
  · intro n g
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hint _) (forall₂_congr fun i j => hint _)
  · intro τ n g
    have hτ : ∀ x : E, τ x ∈ intO E ↔ x ∈ intO E := by
      intro x
      simp only [Valuation.mem_integer_iff, hval]
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hτ _) (forall₂_congr fun i j => hτ _)
  · intro n
    exact Continuous.units_map _ (continuous_id.matrix_map hcont)

end GlobalTheory.CompanionTheory.UnramDict
