import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarEqProductLocalMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerDens

section Real

theorem prod_close {ι : Type} (S : Finset ι) (a : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r : ι → ℝ, (∀ v ∈ S, |r v - a v| ≤ δ) → |∏ v ∈ S, r v - ∏ v ∈ S, a v| ≤ ε := by
  have hc : Continuous (fun r : S → ℝ => ∏ v : S, r v) :=
    continuous_finset_prod _ (fun i _ => continuous_apply i)
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc (fun v => a v) ε hε
  refine ⟨δ / 2, half_pos hδ, fun r hr => ?_⟩
  have hd : dist (fun v : S => r v) (fun v : S => a v) < δ := by
    refine (dist_pi_lt_iff hδ).2 fun v => ?_
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hr v v.2) (half_lt_self hδ)
  have := h _ hd
  rw [Real.dist_eq, Finset.prod_coe_sort S r, Finset.prod_coe_sort S a] at this
  exact this.le

theorem avg_bound {α : Type} [MeasurableSpace α] (μ : Measure α) {U : Set α} (hU : MeasurableSet U)
    (hfin : μ U ≠ ∞) (D : α → ℝ) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hD : ∀ y ∈ U, |D y - c| ≤ ε) :
    |(∫⁻ y in U, ENNReal.ofReal (D y) ∂μ).toReal - c * (μ U).toReal| ≤ ε * (μ U).toReal := by
  have hup : ∫⁻ y in U, ENNReal.ofReal (D y) ∂μ ≤ ENNReal.ofReal (c + ε) * μ U := by
    calc ∫⁻ y in U, ENNReal.ofReal (D y) ∂μ ≤ ∫⁻ _ in U, ENNReal.ofReal (c + ε) ∂μ :=
          setLIntegral_mono' hU fun y hy =>
            ENNReal.ofReal_le_ofReal (by have := abs_le.1 (hD y hy); linarith)
      _ = _ := by rw [setLIntegral_const]
  have hlo : ENNReal.ofReal (c - ε) * μ U ≤ ∫⁻ y in U, ENNReal.ofReal (D y) ∂μ := by
    calc ENNReal.ofReal (c - ε) * μ U = ∫⁻ _ in U, ENNReal.ofReal (c - ε) ∂μ := by
          rw [setLIntegral_const]
      _ ≤ _ := setLIntegral_mono' hU fun y hy =>
            ENNReal.ofReal_le_ofReal (by have := abs_le.1 (hD y hy); linarith)
  have hne : ∫⁻ y in U, ENNReal.ofReal (D y) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hup
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hup
  have h2 := ENNReal.toReal_mono hne hlo
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at h2
  have hL : 0 ≤ (μ U).toReal := ENNReal.toReal_nonneg
  have h3 : (c - ε) * (μ U).toReal ≤ max (c - ε) 0 * (μ U).toReal :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hL
  rw [abs_le]
  constructor <;> nlinarith

end Real

section Box

variable (F : Type) [Field F] [NumberField F]

theorem isOpen_int (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

theorem exists_box (x : Af F) {W : Set (Af F)} (hW : W ∈ 𝓝 x) :
    ∃ (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (N : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)),
      (∀ v, N v ∈ 𝓝 (x v)) ∧
      (∀ v, v ∉ S₀ → N v = (v.adicCompletionIntegers F : Set (Fv F v))) ∧
      ∀ y : Af F, (∀ v, y v ∈ N v) → y ∈ W := by
  classical
  let mk : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → Af F :=
    fun y => ⟨fun v => (y v : v.adicCompletion F), Filter.Eventually.of_forall fun v => (y v).2⟩
  have hmk : Continuous mk :=
    (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => ((v.adicCompletionIntegers F : ValuationSubring _) : Set (v.adicCompletion F)))
      (𝓕 := Filter.cofinite)).continuous
  have hW0 : (fun z => x + z) ⁻¹' W ∈ 𝓝 (0 : Af F) := by
    have hc : Continuous (fun z : Af F => x + z) := continuous_const.add continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hW)
  have hpre : mk ⁻¹' ((fun z => x + z) ⁻¹' W) ∈
      𝓝 (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :=
    hmk.continuousAt.preimage_mem_nhds (by
      have h0 : mk 0 = 0 := rfl
      rw [h0]; exact hW0)
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨T, hT, t, ht, hsub⟩ := hpre
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u ∈ 𝓝 (0 : Fv F v),
      ∀ z : v.adicCompletionIntegers F, (z : Fv F v) ∈ u → z ∈ t v := fun v => by
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    exact ⟨u, by simpa using hu, fun z hz => hut hz⟩
  choose u hu hut using hloc
  have hx : {v : HeightOneSpectrum (𝓞 F) | ¬ x v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 x.2
  refine ⟨hT.toFinset ∪ hx.toFinset, fun v => if v ∈ hT.toFinset ∪ hx.toFinset then
    {y | y - x v ∈ u v ∧ y - x v ∈ (v.adicCompletionIntegers F : Set (Fv F v))}
    else (v.adicCompletionIntegers F : Set (Fv F v)), fun v => ?_, fun v hv => ?_, fun y hy => ?_⟩
  · by_cases hv : v ∈ hT.toFinset ∪ hx.toFinset
    · simp only [if_pos hv]
      have hc : Continuous (fun y : Fv F v => y - x v) := continuous_id.sub continuous_const
      have h0 : x v - x v = 0 := sub_self _
      have hO : (v.adicCompletionIntegers F : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) :=
        (isOpen_int F v).mem_nhds (zero_mem _)
      exact Filter.inter_mem
        (hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hu v))
        (hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hO))
    · simp only [if_neg hv]
      have hxv : x v ∈ v.adicCompletionIntegers F := by
        by_contra hc
        exact hv (Finset.mem_union_right _ (hx.mem_toFinset.2 hc))
      exact (isOpen_int F v).mem_nhds hxv
  · simp only [if_neg hv]
  · have hint : ∀ v, y v - x v ∈ v.adicCompletionIntegers F := fun v => by
      by_cases hv : v ∈ hT.toFinset ∪ hx.toFinset
      · have := hy v
        simp only [if_pos hv] at this
        exact this.2
      · have h1 := hy v
        simp only [if_neg hv] at h1
        have hxv : x v ∈ v.adicCompletionIntegers F := by
          by_contra hc
          exact hv (Finset.mem_union_right _ (hx.mem_toFinset.2 hc))
        exact sub_mem h1 hxv
    let zz : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F := fun v => ⟨y v - x v, hint v⟩
    have hzz : zz ∈ T.pi t := fun v hv => by
      have hv' : v ∈ hT.toFinset ∪ hx.toFinset := Finset.mem_union_left _ (hT.mem_toFinset.2 hv)
      have := hy v
      simp only [if_pos hv'] at this
      exact hut v _ this.1
    have := hsub hzz
    have hy' : x + mk zz = y := by
      refine Subtype.ext (funext fun v => ?_)
      show x v + (y v - x v) = y v
      ring
    simpa [hy'] using this

end Box

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_one_tmul' [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (z : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = algebraMap F R (Algebra.trace F E z) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = (Algebra.lmul F E z).baseChange R := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r e
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem trace_tmul' [FiniteDimensional F E] {R : Type} [CommRing R] [Algebra F R] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h : r ⊗ₜ[F] e = r • ((1 : R) ⊗ₜ[F] e) := by simp [TensorProduct.smul_tmul']
  rw [h, map_smul, trace_one_tmul', smul_eq_mul]

variable {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem trace_map [FiniteDimensional F E] (φ : R →ₐ[F] R') (y : R ⊗[F] E) :
    φ (Algebra.trace R (R ⊗[F] E) y) =
      Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map φ (AlgHom.id F E) y) := by
  induction y with
  | zero => simp
  | tmul r e => simp [trace_tmul']
  | add a c ha hc => simp only [map_add, ha, hc]

theorem map_sigR (σ : E →ₐ[F] E) (φ : R →ₐ[F] R') (z : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ z) =
      sigR R' σ (Algebra.TensorProduct.map φ (AlgHom.id F E) z) := by
  induction z with
  | zero => simp
  | tmul r e => simp [sigR]
  | add a c ha hc => simp only [map_add, ha, hc]

theorem map_gram (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (X : Fin n → Fin M → R ⊗[F] E) (a c : Fin n) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (gramR R σ J X a c) =
      gramR R' σ J (fun a i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X a i)) a c := by
  simp only [gramR, hR, hform, map_sum, map_mul, map_sigR, JR, Matrix.map_apply]
  simp [inclR]

def qF (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X : Fin 1 → Fin M → R ⊗[F] E) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)

theorem map_qF [FiniteDimensional F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (φ : R →ₐ[F] R') (X : Fin 1 → Fin M → R ⊗[F] E) :
    φ (qF R σ J X) =
      qF R' σ J (fun a i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X a i)) := by
  simp only [qF, map_mul, AlgHom.commutes, trace_map, map_gram]

theorem sig_expand {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (p q : R ⊗[F] E) (e : E) :
    sigR R σ p * inclR R e * q =
      ∑ k, ∑ l, ((Algebra.TensorProduct.basis R b).repr p k *
        (Algebra.TensorProduct.basis R b).repr q l) ⊗ₜ[F] (σ (b k) * e * b l) := by
  have hX : ∀ y : R ⊗[F] E, ∑ k, ((Algebra.TensorProduct.basis R b).repr y k) ⊗ₜ[F] b k = y := by
    intro y
    conv_rhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  calc sigR R σ p * inclR R e * q
      = sigR R σ (∑ k, ((Algebra.TensorProduct.basis R b).repr p k) ⊗ₜ[F] b k) * inclR R e *
          (∑ l, ((Algebra.TensorProduct.basis R b).repr q l) ⊗ₜ[F] b l) := by rw [hX, hX]
    _ = _ := by
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [sigR, inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem q_expand [FiniteDimensional F E] {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
    (J : Matrix (Fin M) (Fin M) E) (X : Fin 1 → Fin M → R ⊗[F] E) :
    qF R σ J X = ∑ i, ∑ j, ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr (X 0 i) k *
      (Algebra.TensorProduct.basis R b).repr (X 0 j) l *
        algebraMap F R (1 / 2 * Algebra.trace F E (σ (b k) * J i j * b l)) := by
  simp only [qF, gramR, hR, hform, JR, Matrix.map_apply, sig_expand b, map_sum, Finset.mul_sum,
    trace_tmul', map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem scale_repr {d : ℕ} (b : Module.Basis (Fin d) F E) (a : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((a : R ⊗[F] E) * y) k =
      (a : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

end Alg

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem int_ev (c : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) c).2

theorem q_int_ev [FiniteDimensional F E] {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
    (J : Matrix (Fin M) (Fin M) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ latV b v →
        qF (Fv F v) σ J X ∈ v.adicCompletionIntegers F := by
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j k l,
      algebraMap F (Fv F v) (1 / 2 * Algebra.trace F E (σ (b k) * J i j * b l)) ∈
        v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    exact fun i j k l => int_ev _
  filter_upwards [h] with v hv X hX
  rw [q_expand b]
  exact sum_mem fun i _ => sum_mem fun j _ => sum_mem fun k _ => sum_mem fun l _ =>
    mul_mem (mul_mem (hX 0 i k) (hX 0 j l)) (hv i j k l)

def sA {d M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ) :
    Set (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
  {X | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}

theorem scale_ev {d M : ℕ} (b : Module.Basis (Fin d) F E) {a : ℕ} (ha : 0 < a) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ sA b v a ↔ X ∈ latV b v := by
  filter_upwards [int_ev ((a : F)⁻¹)] with v hv X
  have haF : (a : F) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hinv : algebraMap F (Fv F v) (a : F)⁻¹ * (a : Fv F v) = 1 := by
    rw [← map_natCast (algebraMap F (Fv F v)) a, ← map_mul, inv_mul_cancel₀ haF, map_one]
  constructor
  · intro h p i k
    have h1 := h p i k
    rw [scale_repr] at h1
    have h2 := mul_mem hv h1
    rwa [← mul_assoc, hinv, one_mul] at h2
  · intro h p i k
    rw [scale_repr]
    exact mul_mem (natCast_mem _ a) (h p i k)

end Places

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance instLCv (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (Fv F v) := by
  have h := GlobalTheory.T.completion_is_local_ring F v
  unfold IsLocR at h
  exact h.2.1

local instance instSCv (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (Fv F v) := by
  have h := GlobalTheory.T.completion_is_local_ring F v
  unfold IsLocR at h
  exact h.2.2.1

local instance instBorv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩

local instance instBorf : BorelSpace (Af F) := ⟨rfl⟩

local instance instLCf : LocallyCompactSpace (Af F) := (GlobalTheory.T.adeles_locally_compact_second_countable F).2.1

local instance instSCf : SecondCountableTopology (Af F) := (GlobalTheory.T.adeles_locally_compact_second_countable F).2.2.1

theorem nice_nbhd {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (h : IsStdV v lam)
    {s : Fv F v} {n : Set (Fv F v)} (hn : n ∈ 𝓝 s) :
    ∃ V : Set (Fv F v), IsOpen V ∧ V ⊆ n ∧ 0 < lam V ∧ lam V < ⊤ := by
  haveI := h.1
  obtain ⟨K, hK, hKn, hKc⟩ := local_compact_nhds hn
  refine ⟨interior K, isOpen_interior, interior_subset.trans hKn, ?_, ?_⟩
  · exact isOpen_interior.measure_pos lam ⟨s, mem_interior_iff_mem_nhds.2 hK⟩
  · exact (measure_mono interior_subset).trans_lt hKc.measure_lt_top

theorem sA_cpt_open (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {a : ℕ} (ha : 0 < a) :
    IsCompact (sA (M := M) b v a) ∧ IsOpen (sA (M := M) b v a) := by
  obtain ⟨hTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
  haveI := hTR
  have hlat := (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v
  have hcont : ∀ c : Fv F v ⊗[F] E, Continuous
      (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (i : Fin M) => c * X p i) := fun c =>
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have haF : (a : Fv F v) ≠ 0 := by
    rw [← map_natCast (algebraMap F (Fv F v)) a]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 ha.ne')
  have hac : (a : Fv F v ⊗[F] E) * (((a : Fv F v)⁻¹) ⊗ₜ[F] (1 : E)) = 1 := by
    have h1 : (a : Fv F v ⊗[F] E) = (a : Fv F v) ⊗ₜ[F] (1 : E) := by
      rw [← map_natCast (algebraMap (Fv F v) (Fv F v ⊗[F] E)) a]
      rfl
    rw [h1, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ haF, one_mul]
    rfl
  refine ⟨?_, hlat.2.preimage (hcont _)⟩
  have himg : sA (M := M) b v a = (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (i : Fin M) =>
      (((a : Fv F v)⁻¹) ⊗ₜ[F] (1 : E)) * X p i) '' latV b v := by
    ext X
    constructor
    · intro hX
      refine ⟨_, hX, ?_⟩
      funext p i
      show (((a : Fv F v)⁻¹) ⊗ₜ[F] (1 : E)) * ((a : Fv F v ⊗[F] E) * X p i) = X p i
      rw [← mul_assoc, mul_comm (((a : Fv F v)⁻¹) ⊗ₜ[F] (1 : E)), hac, one_mul]
    · rintro ⟨Y, hY, rfl⟩
      show (fun p i => (a : Fv F v ⊗[F] E) * ((((a : Fv F v)⁻¹) ⊗ₜ[F] (1 : E)) * Y p i)) ∈ latV b v
      simpa only [← mul_assoc, hac, one_mul] using hY
  rw [himg]
  exact hlat.1.image (hcont _)

theorem qF_cont (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (qF (Fv F v) σ J : (Fin 1 → Fin M → Fv F v ⊗[F] E) → Fv F v) := by
  obtain ⟨-, -, -, -, -, htr, -, -, -, hgram⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
  have h1 := hgram 1 M J
  exact continuous_const.mul (htr.comp ((continuous_apply 0).comp ((continuous_apply 0).comp h1)))

def box (S : Finset (HeightOneSpectrum (𝓞 F))) (V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) :
    Set (Af F) :=
  {y | (∀ v ∈ S, y v ∈ V v) ∧ ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

theorem box_open (S : Finset (HeightOneSpectrum (𝓞 F)))
    (V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hV : ∀ v, IsOpen (V v)) :
    IsOpen (box S V) := by
  have h1 : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => isOpen_int F v)
  have h2 : {y : Af F | ∀ v ∈ S, y v ∈ V v} = ⋂ v ∈ S, (fun y : Af F => y v) ⁻¹' V v := by
    ext y
    simp
  have h3 : IsOpen {y : Af F | ∀ v ∈ S, y v ∈ V v} := by
    rw [h2]
    exact isOpen_biInter_finset fun v _ => (hV v).preimage (RestrictedProduct.continuous_eval v)
  exact h3.inter h1

theorem box_meas (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hlam : ∀ v, IsStdV v (lam v)) (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure)
    (hlf1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hV : ∀ v, IsOpen (V v)) :
    lf (box S V) = ∏ v ∈ S, lam v (V v) := by
  have key := GlobalTheory.T.finite_adele_haar_pi_restricted_product F lam hlam lf hlf hlf1 Unit S
    (fun v => (fun f : Unit → Fv F v => f ()) ⁻¹' V v)
    (fun v => (measurable_pi_apply ()) (hV v).measurableSet)
  have e1 : {x : Unit → Af F | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈
        (fun f : Unit → Fv F v => f ()) ⁻¹' V v) ∧
        ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} =
      (MeasurableEquiv.funUnique Unit (Af F)) ⁻¹' box S V := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v hv => h1 v hv, fun v hv => h2 v hv ()⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun v hv => h1 v hv, fun v hv i => h2 v hv⟩
  rw [e1, (measurePreserving_funUnique lf Unit).measure_preimage_equiv] at key
  rw [key]
  refine Finset.prod_congr rfl fun v _ => ?_
  haveI := (hlam v).1
  exact (measurePreserving_funUnique (lam v) Unit).measure_preimage_equiv (V v)

theorem box_tuple (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v))
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure)
    (hlf1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) {a : ℕ} (ha : 0 < a)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hV : ∀ v, IsOpen (V v))
    (hun : ∀ v, v ∉ S → ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ sA b v a ↔ X ∈ latV b v)
    (hint : ∀ v, v ∉ S → ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ latV b v →
      qF (Fv F v) σ J X ∈ v.adicCompletionIntegers F) :
    coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ sA b v a) ∧ qF (Af F) σ J X ∈ box S V} =
      ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v}) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hq : ∀ (X : Fin 1 → Fin M → Af F ⊗[F] E) v, (qF (Af F) σ J X) v = qF (Fv F v) σ J (projV v X) :=
    fun X v => map_qF σ J (evalV F v) X
  have hmeas : ∀ v, MeasurableSet (sA (M := M) b v a ∩ {X | qF (Fv F v) σ J X ∈ V v}) := fun v => by
    obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    haveI := hB 1 M
    exact ((sA_cpt_open σ hcm b v ha).2.inter ((hV v).preimage (qF_cont σ hcm J v))).measurableSet
  rw [← GlobalTheory.T.finite_adele_haar_eq_product_local_measures F E σ hcm d b lam hlam lf hlf hlf1 1 M S _ hmeas]
  congr 1
  ext X
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ⟨h1 v, ?_⟩, fun v hv => (hun v hv _).1 (h1 v)⟩
    show qF (Fv F v) σ J (projV v X) ∈ V v
    rw [← hq]
    exact h2 v hv
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · by_cases hv : v ∈ S
      · exact (h1 v hv).1
      · exact (hun v hv _).2 (h2 v hv)
    · rw [hq]
      exact (h1 v hv).2
    · rw [hq]
      exact hint v hv _ (h2 v hv)

theorem hasProd_fibre_mass : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ a : ℕ, 0 < a → ∀ D : Af F → ℝ, Continuous D → (∀ y, 0 ≤ D y) → (∀ U : Set (Af F), MeasurableSet U → coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (D y) ∂lf) → ∀ β : F, β ≠ 0 → HasProd (fun v => (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal) (D (algebraMap F (Af F) β)) := by
  intro F E _ _ _ _ _ σ hcm M J hJ d b lam hlam m hm lf hlf hlf1 a ha D hDc hD0 hUD β hβ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hUD' : ∀ U : Set (Af F), MeasurableSet U →
      coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ sA b v a) ∧ qF (Af F) σ J X ∈ U} =
        ∫⁻ y in U, ENNReal.ofReal (D y) ∂lf := hUD
  rw [HasProd, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hWn : {y : Af F | |D y - D (algebraMap F (Af F) β)| < ε / 3} ∈ 𝓝 (algebraMap F (Af F) β) :=
    (isOpen_lt (hDc.sub continuous_const).abs continuous_const).mem_nhds (by simpa using hε3)
  obtain ⟨S₀, N, hN, hNoff, hNW⟩ := exists_box F _ hWn
  have hev := (q_int_ev (M := M) b σ J).and (scale_ev (M := M) b ha)
  have hbad := Filter.eventually_cofinite.1 hev
  refine ⟨S₀ ∪ hbad.toFinset, fun S hS => ?_⟩
  have hS' : ∀ v, v ∉ S → v ∉ S₀ ∧ ((∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ latV b v →
        qF (Fv F v) σ J X ∈ v.adicCompletionIntegers F) ∧
      ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ sA b v a ↔ X ∈ latV b v) := fun v hv => by
    refine ⟨fun h => hv (hS (Finset.mem_union_left _ h)), ?_⟩
    by_contra hc
    exact hv (hS (Finset.mem_union_right _ (hbad.mem_toFinset.2 hc)))
  obtain ⟨δ, hδ, hclose⟩ := prod_close S
    (fun v => (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (sA b v a)).toReal) hε3
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Fv F v) β ≠ 0 := fun v =>
    (map_ne_zero (algebraMap F (Fv F v))).2 hβ
  have hloc := fun v => GlobalTheory.T.local_gram_fiber_rank_one_set_formula F E σ hcm M J hJ d b v (lam v) (hlam v) (m v) (hm v)
    (sA b v a) (sA_cpt_open σ hcm b v ha).1 (sA_cpt_open σ hcm b v ha).2
    (algebraMap F (Fv F v) β) (hne v) δ hδ
  choose Uv hUv hUv' using hloc
  have hVex := fun v => nice_nbhd (hlam v) (Filter.inter_mem (hUv v) (hN v))
  choose V hVo hVs hVpos hVfin using hVex
  have hUW : ∀ y ∈ box S V, |D y - D (algebraMap F (Af F) β)| ≤ ε / 3 := fun y hy => by
    refine le_of_lt (hNW y fun v => ?_)
    by_cases hv : v ∈ S
    · exact (hVs v (hy.1 v hv)).2
    · rw [hNoff v (hS' v hv).1]
      exact hy.2 v hv
  have hBo := box_open S V hVo
  have hL := box_meas lam hlam lf hlf hlf1 S V hVo
  have hP := box_tuple σ hcm J b lam hlam lf hlf hlf1 ha S V hVo (fun v hv => (hS' v hv).2.2)
    (fun v hv => (hS' v hv).2.1)
  rw [hUD' _ hBo.measurableSet] at hP
  have hLv : ∀ v, 0 < (lam v (V v)).toReal := fun v =>
    ENNReal.toReal_pos (hVpos v).ne' (hVfin v).ne
  have hLf : (lf (box S V)).toReal = ∏ v ∈ S, (lam v (V v)).toReal := by
    rw [hL, ENNReal.toReal_prod]
  have hLfpos : 0 < (lf (box S V)).toReal := by
    rw [hLf]
    exact Finset.prod_pos fun v _ => hLv v
  have hfin : lf (box S V) ≠ ∞ := by
    rw [hL]
    exact ENNReal.prod_ne_top fun v _ => (hVfin v).ne
  have hI : (∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal =
      ∏ v ∈ S, (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal := by
    rw [hP, ENNReal.toReal_prod]
  have havg := avg_bound lf hBo.measurableSet hfin D (hD0 _) hε3.le hUW
  have hcl := hclose (fun v =>
    (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal /
      (lam v (V v)).toReal) (fun v _ => by
    have h1 := hUv' v (V v) (hVo v).measurableSet (fun y hy => (hVs v hy).1)
    have h2 : (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal /
        (lam v (V v)).toReal - (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (sA b v a)).toReal =
        ((coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal -
          (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (sA b v a)).toReal * (lam v (V v)).toReal) /
          (lam v (V v)).toReal := by
      have := (hLv v).ne'
      field_simp
    show |_ - _| ≤ δ
    rw [h2, abs_div, abs_of_pos (hLv v), div_le_iff₀ (hLv v)]
    exact h1)
  rw [Finset.prod_div_distrib, ← hI, ← hLf] at hcl
  have h3 : |(∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal / (lf (box S V)).toReal -
      D (algebraMap F (Af F) β)| ≤ ε / 3 := by
    have h4 : (∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal / (lf (box S V)).toReal -
        D (algebraMap F (Af F) β) = ((∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal -
          D (algebraMap F (Af F) β) * (lf (box S V)).toReal) / (lf (box S V)).toReal := by
      have := hLfpos.ne'
      field_simp
    rw [h4, abs_div, abs_of_pos hLfpos, div_le_iff₀ hLfpos]
    exact havg
  change dist (∏ v ∈ S, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (sA b v a)).toReal) _ < ε
  rw [Real.dist_eq]
  have h5 := abs_le.1 hcl
  have h6 := abs_le.1 h3
  rw [abs_lt]
  constructor <;> linarith

end Main

end GlobalTheory.CompanionTheory.SW.EulerDens
