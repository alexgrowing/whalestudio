import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralClosureCompletedCMAlgebraCompactOpen
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.SpectralNormIntegrality.SpecInt

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.Ord

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Abs

theorem detect_of_idem {K : Type} [CommRing K] (O : Subring K) (I : Finset K)
    (hid : ∀ e ∈ I, e * e = e)
    (hdom : ∀ e ∈ I, ∀ x y : K, (e * x) * (e * y) = 0 → e * x = 0 ∨ e * y = 0)
    (htot : ∀ e ∈ I, ∀ x y : K, ∃ z ∈ O, e * x = z * (e * y) ∨ e * y = z * (e * x))
    (hsep : ∀ x : K, (∀ e ∈ I, e * x = 0) → x = 0)
    (n M : ℕ) (X : Fin n → Fin M → K) (hX : ¬ LinearIndependent K X) :
    ∃ e ∈ I, ∃ (l : Fin n) (a : Fin n → K), (∀ i, a i ∈ O) ∧ a l = 1 ∧
      ∀ k, e * ∑ i, X i k * a i = 0 := by
  classical
  rw [Fintype.not_linearIndependent_iff] at hX
  obtain ⟨c, hc, i₀, hi₀⟩ := hX
  have hex : ∃ e ∈ I, e * c i₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hi₀ (hsep _ h)
  obtain ⟨e, he, hne⟩ := hex
  have hmax : ∀ s : Finset (Fin n), s.Nonempty →
      ∃ l ∈ s, ∀ i ∈ s, ∃ z ∈ O, e * c i = z * (e * c l) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      refine ⟨a, by simp, fun i hi => ⟨1, O.one_mem, ?_⟩⟩
      rw [Finset.mem_singleton] at hi
      simp [hi]
    | cons a s ha hs ih =>
      obtain ⟨l, hl, h⟩ := ih
      obtain ⟨z, hz, h1 | h1⟩ := htot e he (c a) (c l)
      · refine ⟨l, by simp [hl], fun i hi => ?_⟩
        rw [Finset.mem_cons] at hi
        rcases hi with rfl | hi
        · exact ⟨z, hz, h1⟩
        · exact h i hi
      · refine ⟨a, by simp, fun i hi => ?_⟩
        rw [Finset.mem_cons] at hi
        rcases hi with rfl | hi
        · exact ⟨1, O.one_mem, by simp⟩
        · obtain ⟨w, hw, h2⟩ := h i hi
          exact ⟨w * z, O.mul_mem hw hz, by rw [h2, h1]; ring⟩
  obtain ⟨l, -, hl⟩ := hmax Finset.univ ⟨i₀, Finset.mem_univ _⟩
  choose! z hz hzc using fun i => hl i (Finset.mem_univ i)
  have hl0 : e * c l ≠ 0 := by
    intro h0
    apply hne
    rw [hzc i₀ , h0, mul_zero]
  have hac : ∀ i, (if i = l then 1 else z i) * (e * c l) = e * c i := by
    intro i
    by_cases h : i = l
    · simp [h]
    · simp [h, ← hzc i]
  refine ⟨e, he, l, fun i => if i = l then 1 else z i, ?_, by simp, fun k => ?_⟩
  · intro i
    by_cases h : i = l
    · simp [h, O.one_mem]
    · simp [h, hz i]
  have hk : ∑ i, c i * X i k = 0 := by
    have h1 := congrFun hc k
    simpa [Finset.sum_apply] using h1
  set w := ∑ i, X i k * (if i = l then 1 else z i) with hw
  have hz0 : (e * c l) * (e * w) = 0 := by
    have h2 : (e * c l) * (e * w) = e * ∑ i, c i * X i k * e := by
      rw [hw, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hac i
      calc e * c l * (e * (X i k * (if i = l then 1 else z i)))
          = e * (X i k * ((if i = l then 1 else z i) * (e * c l))) := by ring
        _ = e * (c i * X i k * e) := by rw [this]; ring
    rw [h2, ← Finset.sum_mul, hk, zero_mul, mul_zero]
  exact (hdom e he _ _ hz0).resolve_left hl0

theorem line_dom {k K : Type} [Field k] [CommRing K] [Algebra k K] (φ : K →ₐ[k] k) (e : K) (he : φ e = 1)
    (hl : ∀ x, e * x = φ x • e) (x y : K) (h : (e * x) * (e * y) = 0) : e * x = 0 ∨ e * y = 0 := by
  have hee : e * e = e := by rw [hl e, he, one_smul]
  rw [hl x, hl y, smul_mul_smul_comm, hee, smul_eq_zero] at h
  rw [hl x, hl y]
  rcases h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · left; rw [h, zero_smul]
    · right; rw [h, zero_smul]
  · left; rw [h, smul_zero]

theorem line_tot {k K : Type} [Field k] [CommRing K] [Algebra k K] (A : ValuationSubring k) (O : Subring K)
    (hA : ∀ r ∈ A, algebraMap k K r ∈ O) (φ : K →ₐ[k] k) (e : K)
    (hl : ∀ x, e * x = φ x • e) (x y : K) : ∃ z ∈ O, e * x = z * (e * y) ∨ e * y = z * (e * x) := by
  by_cases hy : φ y = 0
  · exact ⟨0, O.zero_mem, Or.inr (by rw [hl y, hy, zero_smul, zero_mul])⟩
  by_cases hx : φ x = 0
  · exact ⟨0, O.zero_mem, Or.inl (by rw [hl x, hx, zero_smul, zero_mul])⟩
  rcases A.mem_or_inv_mem (φ x / φ y) with h | h
  · refine ⟨_, hA _ h, Or.inl ?_⟩
    rw [hl x, hl y, ← Algebra.smul_def, smul_smul, div_mul_cancel₀ _ hy]
  · refine ⟨_, hA _ h, Or.inr ?_⟩
    rw [hl x, hl y, ← Algebra.smul_def, smul_smul, inv_div, div_mul_cancel₀ _ hx]

theorem field_total {k L : Type} [NontriviallyNormedField k] [IsUltrametricDist k] [CompleteSpace k] [Field L]
    [Algebra k L] [FiniteDimensional k L] (A : ValuationSubring k) (hA : ∀ x : k, ‖x‖ ≤ 1 ↔ x ∈ A) [Algebra A L]
    [IsScalarTower A k L] (x : L) (hx : x ≠ 0) : IsIntegral A x ∨ IsIntegral A x⁻¹ := by
  haveI : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  have key : ∀ y : L, spectralNorm k L y ≤ 1 → IsIntegral A y := by
    intro y hy
    have hyi : IsIntegral k y := Algebra.IsIntegral.isIntegral y
    rw [PositivityTheory.UnitarySelfGeneration.Mend.specInt_isIntegral_iff_coeff A y hyi]
    rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyi)] at hy
    intro n
    exact (hA _).1 (hy n)
  have hmul : spectralNorm k L x * spectralNorm k L x⁻¹ = 1 := by
    have h1 := map_mul (spectralMulAlgNorm k L) x x⁻¹
    rw [mul_inv_cancel₀ hx] at h1
    simp only [spectralMulAlgNorm_def, spectralNorm_one] at h1
    exact h1.symm
  by_cases h : spectralNorm k L x ≤ 1
  · exact Or.inl (key _ h)
  · refine Or.inr (key _ ?_)
    push_neg at h
    have h0 : 0 ≤ spectralNorm k L x⁻¹ := spectralNorm_nonneg _
    nlinarith

theorem inv_notMem {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [FirstCountableTopology K] (O : Subring K) (hc : IsCompact (O : Set K)) (t : Kˣ) (e : K) (he : e ≠ 0)
    (ht : Tendsto (fun j : ℕ => e * (t : K) ^ j) atTop (𝓝 0)) : ((t⁻¹ : Kˣ) : K) ∉ O := by
  intro hi
  have hmem : ∀ j : ℕ, (((t⁻¹ : Kˣ) : K)) ^ j ∈ (O : Set K) := fun j => O.pow_mem hi j
  obtain ⟨w, -, φ, hφ, hw⟩ := hc.tendsto_subseq hmem
  have h1 := (ht.comp hφ.tendsto_atTop).mul hw
  have h2 : ∀ j, ((fun j : ℕ => e * (t : K) ^ j) ∘ φ) j * (((fun j : ℕ => (((t⁻¹ : Kˣ) : K)) ^ j) ∘ φ) j) = e := by
    intro j
    simp only [Function.comp]
    rw [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
  simp only [h2, zero_mul] at h1
  exact he (tendsto_nhds_unique tendsto_const_nhds h1)

theorem contract {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] (O : Subring K) (hc : IsCompact (O : Set K)) (ho : IsOpen (O : Set K)) (t : Kˣ)
    (ht : (t : K) ∈ O) (ht' : ((t⁻¹ : Kˣ) : K) ∉ O) :
    ∃ θ : ℝ≥0, θ < 1 ∧ ∀ Y : Set K, μ ((fun x => (t : K) * x) '' Y) = θ * μ Y := by
  let φ : K ≃+ K :=
    { toFun := fun x => ((t⁻¹ : Kˣ) : K) * x
      invFun := fun x => (t : K) * x
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_add' := mul_add _ }
  have c1 : Continuous φ := continuous_const.mul continuous_id
  have c2 : Continuous φ.symm := continuous_const.mul continuous_id
  let h : K ≃ₜ K := { φ.toEquiv with continuous_toFun := c1, continuous_invFun := c2 }
  haveI hH : (μ.map φ).IsAddHaarMeasure := φ.isAddHaarMeasure_map μ c1 c2
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ
  set c := Measure.addHaarScalarFactor (μ.map φ) μ with hcdef
  have hall : ∀ Y : Set K, μ ((fun x => (t : K) * x) '' Y) = c * μ Y := by
    intro Y
    have h1 : (μ.map φ) Y = μ ((fun x => (t : K) * x) '' Y) := by
      have h2 : (μ.map h.toMeasurableEquiv) Y = μ (h.toMeasurableEquiv ⁻¹' Y) :=
        h.toMeasurableEquiv.map_apply Y
      have h3 : h.toMeasurableEquiv ⁻¹' Y = (fun x => (t : K) * x) '' Y := by
        ext x
        constructor
        · intro hx
          exact ⟨_, hx, by change (t : K) * (((t⁻¹ : Kˣ) : K) * x) = x; simp⟩
        · rintro ⟨y, hy, rfl⟩
          change ((t⁻¹ : Kˣ) : K) * ((t : K) * y) ∈ Y
          simpa using hy
      rw [← h3, ← h2]
      rfl
    rw [← h1, hν]
    simp
  refine ⟨c, ?_, hall⟩
  have hfin : μ (O : Set K) ≠ ⊤ := hc.measure_lt_top.ne
  set T := (fun x => (t : K) * x) '' (O : Set K) with hTdef
  have hT : IsCompact T := hc.image (continuous_const.mul continuous_id)
  have hsub : T ⊆ (O : Set K) := by
    rintro _ ⟨x, hx, rfl⟩
    exact O.mul_mem ht hx
  have h1 : (1 : K) ∉ T := by
    rintro ⟨x, hx, h⟩
    apply ht'
    have : x = ((t⁻¹ : Kˣ) : K) := by
      have := congrArg (fun y => ((t⁻¹ : Kˣ) : K) * y) h
      simpa using this
    rw [← this]
    exact hx
  have hdiff : 0 < μ ((O : Set K) \ T) := (ho.sdiff hT.isClosed).measure_pos μ ⟨1, O.one_mem, h1⟩
  have hadd : μ T + μ ((O : Set K) \ T) = μ (O : Set K) := by
    rw [measure_add_diff hT.measurableSet.nullMeasurableSet, Set.union_eq_right.2 hsub]
  by_contra hge
  push_neg at hge
  have h2 : μ (O : Set K) ≤ μ T := by
    rw [hTdef, hall]
    calc μ (O : Set K) = 1 * μ (O : Set K) := (one_mul _).symm
      _ ≤ c * μ (O : Set K) := by
        gcongr
        exact_mod_cast hge
  have h3 : μ (O : Set K) + μ ((O : Set K) \ T) ≤ μ (O : Set K) := by
    calc _ ≤ μ T + μ ((O : Set K) \ T) := by gcongr
      _ = _ := hadd
  have h4 : μ (O : Set K) < μ (O : Set K) + μ ((O : Set K) \ T) :=
    ENNReal.lt_add_right hfin hdiff.ne'
  exact absurd h3 (not_le.2 h4)

end Abs

section Pair

theorem pair_props {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [FirstCountableTopology K] (O : Subring K) (hc : IsCompact (O : Set K)) (p q : K) (hpq : p * q = 1)
    (hp : p ∈ O) (hpt : Tendsto (fun j : ℕ => p ^ j) atTop (𝓝 0)) (e : K) (he : e * e = e) (he0 : e ≠ 0)
    (heO : e ∈ O) :
    ∃ t : Kˣ, (t : K) ∈ O ∧ ((t⁻¹ : Kˣ) : K) ∉ O ∧ (∀ x, e * x = 0 → (t : K) * x = x) ∧
      Tendsto (fun j : ℕ => e * (t : K) ^ j) atTop (𝓝 0) := by
  have h1 : (p * e + 1 - e) * (q * e + 1 - e) = 1 := by
    linear_combination (e * e) * hpq + (2 - p - q) * he
  have h2 : (q * e + 1 - e) * (p * e + 1 - e) = 1 := by
    rw [mul_comm]; exact h1
  let t : Kˣ := ⟨p * e + 1 - e, q * e + 1 - e, h1, h2⟩
  have ht : (t : K) = p * e + 1 - e := rfl
  have hpow : ∀ j : ℕ, e * (t : K) ^ j = p ^ j * e := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← mul_assoc, ih, ht, pow_succ]
      linear_combination (p ^ j * (p - 1)) * he
  have hlim : Tendsto (fun j : ℕ => e * (t : K) ^ j) atTop (𝓝 0) := by
    simp only [hpow]
    simpa using hpt.mul_const e
  refine ⟨t, ?_, inv_notMem O hc t e he0 hlim, ?_, hlim⟩
  · rw [ht]
    exact O.sub_mem (O.add_mem (O.mul_mem hp heO) O.one_mem) heO
  · intro x hx
    rw [ht]
    linear_combination (p - 1) * hx

end Pair

section Local

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idems (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ I : Finset (Fv F v ⊗[F] E), (∀ e ∈ I, e * e = e ∧ e ≠ 0) ∧
      (∀ e ∈ I, ∀ x y : Fv F v ⊗[F] E, (e * x) * (e * y) = 0 → e * x = 0 ∨ e * y = 0) ∧
      (∀ e ∈ I, ∀ x y : Fv F v ⊗[F] E, ∃ z ∈ (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring,
        e * x = z * (e * y) ∨ e * y = z * (e * x)) ∧
      (∀ x : Fv F v ⊗[F] E, (∀ e ∈ I, e * x = 0) → x = 0) := by
  classical
  letI nf : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI pf : ProperSpace (Fv F v) := Formalism.BasicNotions.Examples₂.LocF.proper v
  haveI uf : IsUltrametricDist (Fv F v) := inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
      (Valued.toNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toDist)
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hσ.2.2.1
  have hnorm : ∀ x : Fv F v, ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F :=
    PositivityTheory.UnitarySelfGeneration.Mend.specInt_norm_le_one_iff_mem F v
  by_cases hs : Nonempty (E →ₐ[F] Fv F v)
  · obtain ⟨τ⟩ := hs
    obtain ⟨-, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hσ
    let ψ₁ : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v :=
      Algebra.TensorProduct.productLeftAlgHom (AlgHom.id (Fv F v) (Fv F v)) τ
    let ψ₂ : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v :=
      Algebra.TensorProduct.productLeftAlgHom (AlgHom.id (Fv F v) (Fv F v)) (τ.comp σ)
    have hc : τ δ ≠ 0 := (map_ne_zero τ).2 hδ
    have h20 : (2 : Fv F v) ≠ 0 := two_ne_zero
    set c := τ δ with hcdef
    let θ : Fv F v ⊗[F] E := (1 : Fv F v) ⊗ₜ[F] δ
    have p1 : ψ₁ θ = c := by simp [ψ₁, θ, hcdef]
    have p2 : ψ₂ θ = -c := by simp [ψ₂, θ, hcdef, hσδ]
    let e₁ : Fv F v ⊗[F] E := (2⁻¹ : Fv F v) • (1 + c⁻¹ • θ)
    let e₂ : Fv F v ⊗[F] E := (2⁻¹ : Fv F v) • (1 - c⁻¹ • θ)
    have v11 : ψ₁ e₁ = 1 := by
      simp only [e₁, map_smul, map_add, map_one, p1, smul_eq_mul]
      field_simp
      norm_num
    have v12 : ψ₂ e₁ = 0 := by
      simp only [e₁, map_smul, map_add, map_one, p2, smul_eq_mul]
      field_simp
      norm_num
    have v21 : ψ₁ e₂ = 0 := by
      simp only [e₂, map_smul, map_sub, map_one, p1, smul_eq_mul]
      field_simp
      norm_num
    have v22 : ψ₂ e₂ = 1 := by
      simp only [e₂, map_smul, map_sub, map_one, p2, smul_eq_mul]
      field_simp
      norm_num
    let f : (Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v × Fv F v := ψ₁.toLinearMap.prod ψ₂.toLinearMap
    have hfr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = Module.finrank (Fv F v) (Fv F v × Fv F v) := by
      rw [Module.finrank_baseChange, hσ.2.2.1]
      simp
    have hsurj : Function.Surjective f := by
      rintro ⟨r, s⟩
      refine ⟨r • e₁ + s • e₂, ?_⟩
      simp [f, v11, v12, v21, v22]
    have hinj : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj
    have hext : ∀ x y : Fv F v ⊗[F] E, ψ₁ x = ψ₁ y → ψ₂ x = ψ₂ y → x = y := by
      intro x y h1 h2
      exact hinj (Prod.ext h1 h2)
    have l1 : ∀ x, e₁ * x = ψ₁ x • e₁ := by
      intro x
      refine hext _ _ ?_ ?_
      · simp [v11]
      · simp [v12]
    have l2 : ∀ x, e₂ * x = ψ₂ x • e₂ := by
      intro x
      refine hext _ _ ?_ ?_
      · simp [v21]
      · simp [v22]
    have hsum : e₁ + e₂ = 1 := by
      refine hext _ _ ?_ ?_
      · simp [v11, v21]
      · simp [v12, v22]
    have hL : ∀ e ∈ ({e₁, e₂} : Finset (Fv F v ⊗[F] E)),
        ∃ φ : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v, φ e = 1 ∧ ∀ x, e * x = φ x • e := by
      intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact ⟨ψ₁, v11, l1⟩
      · exact ⟨ψ₂, v22, l2⟩
    have hA : ∀ r ∈ v.adicCompletionIntegers F, algebraMap (Fv F v) (Fv F v ⊗[F] E) r ∈
        (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring := by
      intro r hr
      have h := isIntegral_algebraMap (R := v.adicCompletionIntegers F) (A := Fv F v ⊗[F] E)
        (x := (⟨r, hr⟩ : v.adicCompletionIntegers F))
      rwa [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers F) (Fv F v) (Fv F v ⊗[F] E)] at h
    refine ⟨{e₁, e₂}, ?_, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨φ, h1, h2⟩ := hL e he
      refine ⟨by rw [h2 e, h1, one_smul], fun h0 => ?_⟩
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    · intro e he x y h
      obtain ⟨φ, h1, h2⟩ := hL e he
      exact line_dom φ e h1 h2 x y h
    · intro e he x y
      obtain ⟨φ, h1, h2⟩ := hL e he
      exact line_tot (v.adicCompletionIntegers F) _ hA φ e h2 x y
    · intro x h
      have h1 := h e₁ (by simp)
      have h2 := h e₂ (by simp)
      calc x = (e₁ + e₂) * x := by rw [hsum, one_mul]
        _ = 0 := by rw [add_mul, h1, h2, add_zero]
  · have hf : IsField (Fv F v ⊗[F] E) :=
      GlobalTheory.CompanionTheory.DictLoc.isField_tensor_of_no_algHom hσ.2.2.1 (not_nonempty_iff.1 hs)
    letI fK : Field (Fv F v ⊗[F] E) := hf.toField
    haveI : FiniteDimensional (Fv F v) (Fv F v ⊗[F] E) := inferInstance
    refine ⟨{1}, ?_, ?_, ?_, ?_⟩
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact ⟨one_mul _, one_ne_zero⟩
    · intro e he x y h
      rw [Finset.mem_singleton] at he
      subst he
      rw [one_mul, one_mul] at *
      exact mul_eq_zero.1 h
    · intro e he x y
      rw [Finset.mem_singleton] at he
      subst he
      simp only [one_mul]
      by_cases hy : y = 0
      · exact ⟨0, Subring.zero_mem _, Or.inr (by simp [hy])⟩
      by_cases hx : x = 0
      · exact ⟨0, Subring.zero_mem _, Or.inl (by simp [hx])⟩
      rcases field_total (v.adicCompletionIntegers F) hnorm (x / y) (div_ne_zero hx hy) with h | h
      · exact ⟨x / y, h, Or.inl (by field_simp)⟩
      · refine ⟨(x / y)⁻¹, h, Or.inr (by field_simp)⟩
    · intro x h
      simpa using h 1 (Finset.mem_singleton_self _)

theorem exists_unif (v : HeightOneSpectrum (𝓞 F)) :
    ∃ w : Fv F v, w ≠ 0 ∧ w ∈ v.adicCompletionIntegers F ∧ Tendsto (fun j : ℕ => w ^ j) atTop (𝓝 0) := by
  letI nf : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨w, h0, h1⟩ := NormedField.exists_norm_lt_one (Fv F v)
  exact ⟨w, norm_pos_iff.1 h0, (PositivityTheory.UnitarySelfGeneration.Mend.specInt_norm_le_one_iff_mem F v w).1 h1.le,
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1⟩

theorem isIntegral_of_idem {A K : Type} [CommRing A] [CommRing K] [Algebra A K] (e : K) (he : e * e = e) :
    IsIntegral A e := by
  have hd : (Polynomial.X : Polynomial A).degree < ((1 + 1 : ℕ) : WithBot ℕ) :=
    (Polynomial.degree_X_le (R := A)).trans_lt (by norm_cast)
  refine ⟨Polynomial.X ^ (1 + 1) - Polynomial.X, Polynomial.monic_X_pow_sub hd, ?_⟩
  simp [pow_two, he]

end Local

end GlobalTheory.CompanionTheory.AvgFree.Ord

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory in

theorem GlobalTheory.CompanionTheory.AvgFree.exists_ordData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∃ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv
  classical
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI := hlv.1
  haveI : (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv).IsAddHaarMeasure :=
    (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1).1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hσ.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  obtain ⟨hOc, hOo⟩ := GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure F E σ hσ v
  obtain ⟨I, h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.AvgFree.Ord.exists_idems σ hσ v
  obtain ⟨w, hw0, hwA, hwt⟩ := GlobalTheory.CompanionTheory.AvgFree.Ord.exists_unif (F := F) v
  let O : Subring (Fv F v ⊗[F] E) := (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring
  have hOc' : IsCompact (O : Set (Fv F v ⊗[F] E)) := hOc
  have hOo' : IsOpen (O : Set (Fv F v ⊗[F] E)) := hOo
  let p : Fv F v ⊗[F] E := algebraMap (Fv F v) (Fv F v ⊗[F] E) w
  let q : Fv F v ⊗[F] E := algebraMap (Fv F v) (Fv F v ⊗[F] E) w⁻¹
  have hpq : p * q = 1 := by
    simp only [p, q]
    rw [← map_mul, mul_inv_cancel₀ hw0, map_one]
  have hp : p ∈ O := by
    have h := isIntegral_algebraMap (R := v.adicCompletionIntegers F) (A := Fv F v ⊗[F] E)
      (x := (⟨w, hwA⟩ : v.adicCompletionIntegers F))
    rwa [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers F) (Fv F v) (Fv F v ⊗[F] E)] at h
  have hpt : Filter.Tendsto (fun j : ℕ => p ^ j) Filter.atTop (nhds 0) := by
    have hcont : Continuous (algebraMap (Fv F v) (Fv F v ⊗[F] E)) := continuous_algebraMap _ _
    have h := (hcont.tendsto 0).comp hwt
    simpa [Function.comp_def, p, map_pow] using h
  have hpair : ∀ e ∈ I, ∃ t : (Fv F v ⊗[F] E)ˣ, (t : Fv F v ⊗[F] E) ∈ O ∧ ((t⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∉ O ∧
      (∀ x, e * x = 0 → (t : Fv F v ⊗[F] E) * x = x) ∧
      Filter.Tendsto (fun j : ℕ => e * (t : Fv F v ⊗[F] E) ^ j) Filter.atTop (nhds 0) := fun e he =>
    GlobalTheory.CompanionTheory.AvgFree.Ord.pair_props O hOc' p q hpq hp hpt e (h1 e he).1 (h1 e he).2
      (GlobalTheory.CompanionTheory.AvgFree.Ord.isIntegral_of_idem e (h1 e he).1)
  choose! t ht using hpair
  refine ⟨O, I.image fun e => (t e, e), hOc', hOo', ?_, ?_, ?_⟩
  · intro x hx
    have hx' : IsIntegral (v.adicCompletionIntegers F) x := hx
    exact hx'.map ((Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).restrictScalars
      (v.adicCompletionIntegers F))
  · intro r hr
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨g1, g2, g3, g4⟩ := ht e he
    obtain ⟨θ, hθ, hY⟩ := GlobalTheory.CompanionTheory.AvgFree.Ord.contract (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) O hOc' hOo' (t e) g1 g2
    exact ⟨g1, (h1 e he).2, g3, g4, θ, hθ, hY⟩
  · intro n M X hX
    obtain ⟨e, he, l, a, ha, hl, hk⟩ := GlobalTheory.CompanionTheory.AvgFree.Ord.detect_of_idem O I (fun e he => (h1 e he).1) h2 h3 h4 n M X hX
    exact ⟨(t e, e), Finset.mem_image_of_mem _ he, l, a, ha, hl, hk⟩
