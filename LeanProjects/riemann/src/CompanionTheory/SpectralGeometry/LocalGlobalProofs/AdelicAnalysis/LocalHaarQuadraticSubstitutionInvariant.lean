import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero

namespace GlobalTheory.CompanionTheory.SW.QuadIso

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]

def vball (x : K) (γ : ℤᵐ⁰) : Set K := {y | Valued.v (y - x) < γ}

lemma vball_eq_of_mem {x y : K} {γ : ℤᵐ⁰} (h : y ∈ vball x γ) : vball y γ = vball x γ := by
  ext z
  simp only [vball, Set.mem_setOf_eq] at h ⊢
  constructor
  · intro hz
    have : z - x = (z - y) + (y - x) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hz h
  · intro hz
    have : z - y = (z - x) + (-(y - x)) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hz (by rwa [Valuation.map_neg])

def IsRadius (K : Type) [Field K] [Valued K ℤᵐ⁰] (γ : ℤᵐ⁰) : Prop :=
  ∃ u : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v : Valuation K ℤᵐ⁰)))ˣ,
    MonoidWithZeroHom.ValueGroup₀.embedding u.1 = γ

lemma IsRadius.ne_zero {γ : ℤᵐ⁰} (h : IsRadius K γ) : γ ≠ 0 := by
  obtain ⟨u, rfl⟩ := h
  exact map_ne_zero _ |>.2 u.ne_zero

lemma isOpen_ball_of_isRadius {γ : ℤᵐ⁰} (h : IsRadius K γ) : IsOpen {y : K | Valued.v y < γ} := by
  obtain ⟨u, rfl⟩ := h
  have := Valued.isOpen_ball K u.1
  simpa only [Valuation.restrict_lt_iff_lt_embedding] using this

lemma isOpen_vball (x : K) {γ : ℤᵐ⁰} (h : IsRadius K γ) : IsOpen (vball x γ) :=
  (isOpen_ball_of_isRadius h).preimage (continuous_sub_right x)

lemma isTopologicalBasis_vball :
    TopologicalSpace.IsTopologicalBasis {s : Set K | ∃ (x : K) (γ : ℤᵐ⁰), s = vball x γ ∧ IsRadius K γ} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨x, γ, rfl, hγ⟩
    exact isOpen_vball x hγ
  · intro a u ha hu
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (hu.mem_nhds ha)
    have hr : IsRadius K (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) := ⟨γ, rfl⟩
    refine ⟨vball a _, ⟨a, _, rfl, hr⟩, ?_, ?_⟩
    · simpa [vball] using zero_lt_iff.2 hr.ne_zero
    · intro y hy
      apply hγ
      simpa only [vball, Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] using hy

lemma isPiSystem_vball :
    IsPiSystem {s : Set K | ∃ (x : K) (γ : ℤᵐ⁰), s = vball x γ ∧ IsRadius K γ} := by
  rintro _ ⟨x, γ, rfl, hγ⟩ _ ⟨y, δ, rfl, hδ⟩ ⟨z, hzx, hzy⟩
  rcases le_total γ δ with h | h
  · refine ⟨x, γ, ?_, hγ⟩
    rw [← vball_eq_of_mem hzx, ← vball_eq_of_mem hzy]
    refine Set.inter_eq_left.2 fun w hw => lt_of_lt_of_le hw h
  · refine ⟨y, δ, ?_, hδ⟩
    rw [← vball_eq_of_mem hzx, ← vball_eq_of_mem hzy]
    refine Set.inter_eq_right.2 fun w hw => lt_of_lt_of_le hw h

lemma le_exp_neg_one {x : ℤᵐ⁰} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

lemma quad_sub (a c t t' : K) :
    (a * t + c * t ^ 2) - (a * t' + c * t' ^ 2) = (t - t') * (a + c * (t + t')) := by ring

lemma v_lin_eq_one {a c s : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hs : Valued.v s < 1) : Valued.v (a + c * s) = 1 := by
  have : Valued.v (c * s) < Valued.v a := by
    rw [ha, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hs
  rw [Valuation.map_add_eq_of_lt_left _ this, ha]

lemma v_quad_sub {a c t t' : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (ht : Valued.v t < 1) (ht' : Valued.v t' < 1) :
    Valued.v ((a * t + c * t ^ 2) - (a * t' + c * t' ^ 2)) = Valued.v (t - t') := by
  rw [quad_sub, map_mul, v_lin_eq_one ha hc (Valuation.map_add_lt _ ht ht'), mul_one]

lemma v_quad_lt {a c t : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (ht : Valued.v t < 1) : Valued.v (a * t + c * t ^ 2) < 1 := by
  have := v_quad_sub ha hc ht (t' := 0) (by simp)
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, sub_zero] at this
  rwa [this]

lemma exists_approx {a c x : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hx : Valued.v x < 1) (n : ℕ) :
    ∃ t : K, Valued.v t < 1 ∧
      Valued.v ((a * t + c * t ^ 2) - x) ≤ WithZero.exp (-(n + 1 : ℤ)) := by
  induction n with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa using le_exp_neg_one hx
  | succ n ih =>
    obtain ⟨t, ht, he⟩ := ih
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha
      exact zero_ne_one ha
    set e := (a * t + c * t ^ 2) - x with he_def
    have hlt : Valued.v e < 1 := Valuation.map_sub_lt _ (v_quad_lt ha hc ht) hx
    have hae : Valued.v (a⁻¹ * e) = Valued.v e := by
      rw [map_mul, map_inv₀, ha]; simp
    have ht' : Valued.v (t - a⁻¹ * e) < 1 := Valuation.map_sub_lt _ ht (by rwa [hae])
    refine ⟨t - a⁻¹ * e, ht', ?_⟩
    have key : (a * (t - a⁻¹ * e) + c * (t - a⁻¹ * e) ^ 2) - x =
        -(a⁻¹ * e * c * (t + (t - a⁻¹ * e))) := by
      have h1 : a * (a⁻¹ * e) = e := by field_simp
      have h2 : x = (a * t + c * t ^ 2) - e := by rw [he_def]; ring
      rw [h2]
      linear_combination (-1 : K) * h1
    rw [key, Valuation.map_neg, map_mul, map_mul, hae]
    have hs : Valued.v (t + (t - a⁻¹ * e)) ≤ WithZero.exp (-1 : ℤ) :=
      le_exp_neg_one (Valuation.map_add_lt _ ht ht')
    calc Valued.v e * Valued.v c * Valued.v (t + (t - a⁻¹ * e))
        ≤ WithZero.exp (-(n + 1 : ℤ)) * 1 * WithZero.exp (-1 : ℤ) := by gcongr
      _ = WithZero.exp (-((n + 1 : ℕ) + 1 : ℤ)) := by
        rw [mul_one, ← WithZero.exp_add]
        congr 1

lemma exists_near {a c x : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hx : Valued.v x < 1) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    ∃ t : K, Valued.v t < 1 ∧ Valued.v ((a * t + c * t ^ 2) - x) < γ := by
  obtain ⟨t, ht, h⟩ := exists_approx ha hc hx (WithZero.log γ).natAbs.succ
  refine ⟨t, ht, lt_of_le_of_lt h ?_⟩
  conv_rhs => rw [← WithZero.exp_log hγ]
  rw [WithZero.exp_lt_exp]
  have := neg_abs_le (WithZero.log γ)
  push_cast
  omega

variable [MeasurableSpace K] [BorelSpace K]

lemma measure_ball (lam : Measure K) [lam.IsAddLeftInvariant] {a c : K}
    (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1) (x : K) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    lam ((fun t => a * t + c * t ^ 2) ⁻¹' vball x γ ∩ {s | Valued.v s < 1}) =
      lam (vball x γ ∩ {s | Valued.v s < 1}) := by
  by_cases hne : (vball x γ ∩ {s : K | Valued.v s < 1}).Nonempty
  · obtain ⟨y, hyB, hyM⟩ := hne
    rw [← vball_eq_of_mem hyB]
    rcases le_or_gt 1 γ with h1 | h1
    · have hsub : ∀ s : K, Valued.v s < 1 → s ∈ vball y γ := fun s hs =>
        lt_of_lt_of_le (Valuation.map_sub_lt _ hs hyM) h1
      congr 1
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hsub _ h.2, h.2⟩, fun h => ⟨hsub _ (v_quad_lt ha hc h.2), h.2⟩⟩
    · obtain ⟨t₀, ht₀, hnear⟩ := exists_near ha hc hyM hγ
      have hB : vball y γ = vball (a * t₀ + c * t₀ ^ 2) γ := (vball_eq_of_mem hnear).symm
      have hsubM : ∀ (z : K), Valued.v z < 1 → vball z γ ⊆ {s : K | Valued.v s < 1} := by
        intro z hz s hs
        have : s = (s - z) + z := by ring
        rw [Set.mem_setOf_eq, this]
        exact Valuation.map_add_lt _ (lt_trans hs h1) hz
      have e1 : (fun t => a * t + c * t ^ 2) ⁻¹' vball y γ ∩ {s | Valued.v s < 1} = vball t₀ γ := by
        rw [hB]
        ext t
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h, hM⟩
          simpa only [vball, Set.mem_setOf_eq, v_quad_sub ha hc hM ht₀] using h
        · intro h
          have hM := hsubM t₀ ht₀ h
          refine ⟨?_, hM⟩
          simpa only [vball, Set.mem_setOf_eq, v_quad_sub ha hc hM ht₀] using h
      have e2 : vball y γ ∩ {s | Valued.v s < 1} = vball y γ :=
        Set.inter_eq_left.2 (hsubM y hyM)
      rw [e1, e2]
      have e3 : vball t₀ γ = (fun h => (y - t₀) + h) ⁻¹' vball y γ := by
        ext h
        simp only [vball, Set.mem_preimage, Set.mem_setOf_eq]
        have : y - t₀ + h - y = h - t₀ := by ring
        rw [this]
      rw [e3, measure_preimage_add]
  · have hem : (fun t => a * t + c * t ^ 2) ⁻¹' vball x γ ∩ {s | Valued.v s < 1} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨h, hM⟩
      exact hne ⟨_, h, v_quad_lt ha hc hM⟩
    rw [hem, Set.not_nonempty_iff_eq_empty.1 hne]

theorem measure_quad [SecondCountableTopology K] [IsTopologicalRing K] (lam : Measure K) [lam.IsAddLeftInvariant]
    (hfin : lam {s | Valued.v s < 1} ≠ ⊤) {a c : K}
    (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1) {A : Set K} (hA : MeasurableSet A) :
    lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  have hMo : IsOpen {s : K | Valued.v s < 1} := isOpen_ball_of_isRadius ⟨1, by simp⟩
  have hM : MeasurableSet {s : K | Valued.v s < 1} := hMo.measurableSet
  have hf : Measurable (fun t : K => a * t + c * t ^ 2) := by
    apply Continuous.measurable
    fun_prop
  haveI : IsFiniteMeasure (lam.restrict {s | Valued.v s < 1}) :=
    ⟨by simpa using hfin.lt_top⟩
  haveI : IsFiniteMeasure ((lam.restrict {s | Valued.v s < 1}).map fun t : K => a * t + c * t ^ 2) :=
    Measure.isFiniteMeasure_map _ _
  have hmeas : (lam.restrict {s | Valued.v s < 1}).map (fun t : K => a * t + c * t ^ 2) =
      lam.restrict {s | Valued.v s < 1} := by
    refine ext_of_generate_finite _
      (BorelSpace.measurable_eq.trans isTopologicalBasis_vball.borel_eq_generateFrom)
      isPiSystem_vball ?_ ?_
    · rintro _ ⟨x, γ, rfl, hγ⟩
      have hB := (isOpen_vball x hγ).measurableSet
      rw [Measure.map_apply hf hB, Measure.restrict_apply (hf hB), Measure.restrict_apply hB]
      exact measure_ball lam ha hc x hγ.ne_zero
    · rw [Measure.map_apply hf MeasurableSet.univ]
      simp
  have key : ((lam.restrict {s | Valued.v s < 1}).map fun t : K => a * t + c * t ^ 2) A =
      lam.restrict {s | Valued.v s < 1} A := by rw [hmeas]
  rw [Measure.map_apply hf hA, Measure.restrict_apply (hf hA), Measure.restrict_apply hA] at key
  rw [← key]
  congr 1
  ext t
  simp [and_comm]

end GlobalTheory.CompanionTheory.SW.QuadIso

theorem GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ a c : Fv F v, Valued.v a = 1 → c ∈ v.adicCompletionIntegers F → ∀ A : Set (Fv F v), MeasurableSet A → lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  intro F _ _ v lam hlam _ a c ha hc A hA
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hH, h1⟩ := hlam
  haveI := hH
  obtain ⟨_, _, hsc, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := hsc
  have hfin : lam {s : Fv F v | Valued.v s < 1} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
    rw [← h1]
    refine measure_mono fun s hs => ?_
    exact (Valuation.mem_integer_iff _ _).2 (le_of_lt hs)
  exact GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad lam hfin ha hc hA
