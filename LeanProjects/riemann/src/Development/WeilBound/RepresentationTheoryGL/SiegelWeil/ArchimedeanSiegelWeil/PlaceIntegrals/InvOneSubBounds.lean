import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.ZeroBlockCoefficientInductionLeftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContentZetaSeriesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorsContentDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIsotropicOrbitOfE0Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingLatticeMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneZeroFibreVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSiegelWeilUnramifiedMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficientStatement
namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
theorem finite_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ p : ℕ, 1 ≤ p → 2 * p < M → ∀ (h₀ : ∀ a b : Fin p, σ ((0 : Matrix (Fin p) (Fin p) E) b a) = (0 : Matrix (Fin p) (Fin p) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ p → Measure (Fin p → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J p (coordW (Fv F v) b lam p M) (coordHerm (Fv F v) σ b lam p) m → m (hermOf (Fv F v) σ (0 : Matrix (Fin p) (Fin p) E) h₀) (latV b v) < ⊤ := by
  intro F E _ _ _ _ _ σ hσ M J hJ p hp hM h₀ d b v lam hlam m hm
  have hL := GlobalTheory.T.contDiffOn_chart_globalWhittakerCoefficient F E σ hσ d b p M v
  exact lt_top_iff_ne_top.2 (GlobalTheory.T.local_siegel_weil_unramified_measure F E σ hσ M J hJ p hp hM d b v lam hlam m hm _ (latV b v) hL.1 hL.2).2.1

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

theorem lintegral_pieces {V ι : Type} [MeasurableSpace V] [Countable ι] (μ : Measure V) (A : ι → Set V)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A)) (Ψ : V → ℝ≥0∞)
    (κ : ι → ℝ≥0∞) (hv : ∀ i, ∀ y ∈ A i, Ψ y = κ i) (h0 : ∀ᵐ y ∂μ, y ∉ ⋃ i, A i → Ψ y = 0) :
    ∫⁻ y, Ψ y ∂μ = ∑' i, κ i * μ (A i) := by
  have hU : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  rw [← lintegral_add_compl Ψ hU]
  have h2 : ∫⁻ y in (⋃ i, A i)ᶜ, Ψ y ∂μ = 0 := by
    have : ∫⁻ y in (⋃ i, A i)ᶜ, Ψ y ∂μ = ∫⁻ _ in (⋃ i, A i)ᶜ, 0 ∂μ := by
      refine lintegral_congr_ae ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' hU.compl]
      filter_upwards [h0] with y hy hyc
      exact hy hyc
    simpa using this
  rw [h2, add_zero, lintegral_iUnion hA hd]
  refine tsum_congr fun i => ?_
  rw [setLIntegral_congr_fun (g := fun _ => κ i) (hA i) (fun y hy => hv i y hy), setLIntegral_const]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

theorem hermOf_zero_val (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] (p : ℕ) (h : ∀ a b : Fin p, σ ((0 : Matrix (Fin p) (Fin p) E) b a) = (0 : Matrix (Fin p) (Fin p) E) a b) :
    ((hermOf R σ (0 : Matrix (Fin p) (Fin p) E) h : HermR R σ p) : Matrix (Fin p) (Fin p) (R ⊗[F] E)) = 0 := by
  funext i j
  simp [hermOf]

theorem pow_index (a : ℝ≥0) (ha : a ≠ 0) (n N : ℕ) (hn : n ≤ N) :
    (a : ℝ≥0∞) ^ n * ENNReal.ofReal ((((a : ℝ))⁻¹) ^ N) = ENNReal.ofReal ((((a : ℝ))⁻¹) ^ (N - n)) := by
  have hpos : (0 : ℝ) < a := by exact_mod_cast pos_iff_ne_zero.2 ha
  rw [show (a : ℝ≥0∞) ^ n = ENNReal.ofReal ((a : ℝ) ^ n) by
    rw [ENNReal.ofReal_pow hpos.le, ENNReal.ofReal_coe_nnreal],
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add, inv_pow, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

theorem stageInt_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M n d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (lam : Measure (Fv F v)) (m' : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J))
    (hg : actW (Fv F v) σ (hypOne J) g (e0 _ M) ∉ latV b v) :
    stageInt (Fv F v) σ J b lam m' ((latV b v).indicator 1) g = 0 := by
  have hz : ∀ (Y : Fin n → Fin M → Fv F v ⊗[F] E) (a : Fin 1 → Fin n → Fv F v ⊗[F] E),
      ((latV b v).indicator 1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
        (actW (Fv F v) σ (hypOne J) g (consA a Y)) = 0 := by
    intro Y a
    refine Set.indicator_of_notMem (fun hmem => hg ?_) _
    intro p i k
    have h := hmem 0 i k
    have e : actW (Fv F v) σ (hypOne J) g (e0 _ M) p = actW (Fv F v) σ (hypOne J) g (consA a Y) 0 := rfl
    rw [e]
    exact h
  simp [stageInt, hz]

theorem good_local (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hn1 : 1 ≤ n)
    (hnM : 2 * n < M)
    (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b)
    (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b)
    (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b)
    (d : ℕ) (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), IsStdV v lam →
      ∀ (m : HermR (Fv F v) σ (n + 1) → Measure (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E))
        (m₁ : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E))
        (m' : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibFree (Fv F v) σ (hypOne J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 2)) (coordHerm (Fv F v) σ b lam (n + 1)) m →
      IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b lam 1 (M + 2)) (coordHerm (Fv F v) σ b lam 1) m₁ →
      IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' →
      m (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v) =
          m' (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v) *
            m₁ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v) *
            ENNReal.ofReal (zetaV E v (M + 1 - n)) ∧
        m₁ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) =
          m₁ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v) *
            ENNReal.ofReal (zetaV E v (M + 1)) := by
  have hJ' : IsHermND σ (hypOne J) := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem F E σ hσ M J hJ).1
  filter_upwards [GlobalTheory.T.local_content_zeta_series F E σ hσ d b, GlobalTheory.T.primitive_vectors_content_decomposition F E σ hσ M J hJ d b] with v hc hp lam hlam m m₁ m' hm hm₁ hm'
  obtain ⟨ι, hι, c, w, hC, hZ⟩ := hc
  obtain ⟨pM, pL, pD, pE⟩ := hp ι c w hC
  obtain ⟨c1, c2, c3, -, -⟩ := hC
  have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨r1, r2, r3, r4, -⟩ := id hloc
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 (M + 2)
  set S₁ := hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ with hS₁
  set P := primV σ J b v with hP
  let A : ι → Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) := fun i => {y | ∃ y₀ ∈ P, y = scalT (c i) y₀}
  haveI := a8 (n + 1) (M + 2)
  have hlatM : MeasurableSet (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 (M + 2) v).2.1.measurableSet
  have hlatM' : MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b (n + 1) (M + 2) v).2.1.measurableSet

  have hinv : ∀ i, ∃ u : Fv F v ⊗[F] E, u * c i = 1 := fun i => by
    obtain ⟨x, hx⟩ := (c1 i).1
    exact ⟨(x⁻¹ : (Fv F v ⊗[F] E)ˣ), by rw [← hx]; exact x.inv_mul⟩
  choose u hu using hinv
  have hscal : ∀ (x y : Fv F v ⊗[F] E) (z : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E),
      scalT x (scalT y z) = scalT (x * y) z := fun x y z => by
    funext p i
    simp [scalT, mul_assoc]
  have hone : ∀ z : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, scalT (1 : Fv F v ⊗[F] E) z = z := fun z => by
    funext p i
    simp [scalT]
  have hAset : ∀ i, A i = (scalT (u i)) ⁻¹' P := fun i => by
    ext y
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      show scalT (u i) (scalT (c i) y₀) ∈ P
      rw [hscal, hu, hone]
      exact hy₀
    · intro hy
      refine ⟨scalT (u i) y, hy, ?_⟩
      rw [hscal, mul_comm, hu, hone]
  have hcont : ∀ x : Fv F v ⊗[F] E, Continuous (scalT x : (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → _) := fun x =>
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have hAm : ∀ i, MeasurableSet (A i) := fun i => by
    rw [hAset]
    exact (hcont (u i)).measurable pM
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro y ⟨y₀, hy₀, rfl⟩ ⟨y₁, hy₁, he⟩
    exact hij (pD i j y₀ hy₀ y₁ hy₁ he)
  have hfree : ∀ᵐ y ∂(m₁ S₁), LinearIndependent (Fv F v ⊗[F] E) y ∧ gramR (Fv F v) σ (hypOne J) y = 0 := by
    have h := hm₁.1 S₁
    have h2 := compl_mem_ae_iff.2 h
    rw [compl_compl] at h2
    filter_upwards [h2] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨hy2, ?_⟩
    have h3 : gramR (Fv F v) σ (hypOne J) y = ((S₁ : HermR (Fv F v) σ 1) : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) := hy1
    rw [h3, hS₁, hermOf_zero_val]
  have hlatE : ∀ᵐ y ∂(m₁ S₁), y ∉ ⋃ i, A i → y ∉ latV b v := by
    filter_upwards [hfree] with y hy hyA hyl
    obtain ⟨i, y₀, hy₀, he⟩ := pE y hy.1 hy.2 hyl
    exact hyA (Set.mem_iUnion.2 ⟨i, y₀, hy₀, he⟩)
  have hAl : ∀ i, ∀ y ∈ A i, y ∈ latV b v := by
    rintro i y ⟨y₀, hy₀, rfl⟩
    exact pL i y₀ hy₀

  have e1 : m₁ S₁ (latV b v) = ∑' i, m₁ S₁ (A i) := by
    have h := lintegral_pieces (m₁ S₁) A hAm hAd ((latV b v).indicator 1) (fun _ => 1)
      (fun i y hy => by simp [Set.indicator_of_mem (hAl i y hy)])
      (by
        filter_upwards [hlatE] with y hy hyA
        simp [Set.indicator_of_notMem (hy hyA)])
    rw [lintegral_indicator_one hlatM] at h
    simpa using h

  have e2 : ∀ i, m₁ S₁ (A i) = m₁ S₁ P * ENNReal.ofReal ((((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) ^ (M + 1)) := by
    intro i
    obtain ⟨t, ht1, ht2⟩ := c3 i
    have hq0 : qv v ≠ 0 := by
      intro h0
      have : Ideal.absNorm v.asIdeal = 0 := by simpa [qv] using h0
      exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)
    have ha : qv v ^ w i ≠ 0 := pow_ne_zero _ hq0
    have hs := GlobalTheory.T.local_rank_one_zero_fibre_volume F E σ hσ (M + 2) (hypOne J) hJ' (by omega) h₂ d b v lam hlam m₁ hm₁ (c i) (qv v ^ w i) t
      (c1 i).1 ha (c2 i lam hlam) ht1 (by rw [ht2]; push_cast; rfl) (A i) (hAm i)
    have hset : {y | scalT (c i) y ∈ A i} = P := by
      ext y
      constructor
      · rintro ⟨y₀, hy₀, he⟩
        have : scalT (u i) (scalT (c i) y) = scalT (u i) (scalT (c i) y₀) := by rw [he]
        rw [hscal, hscal, hu, hone, hone] at this
        exact this ▸ hy₀
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [hset] at hs
    have hpos : (0 : ℝ) < ((qv v ^ w i : ℝ≥0) : ℝ) := by exact_mod_cast pos_iff_ne_zero.2 ha
    have hN : M + 2 - 1 = M + 1 := by omega
    rw [hN] at hs
    rw [hs, mul_comm ((((qv v ^ w i : ℝ≥0) : ℝ≥0∞)) ^ (M + 1)), mul_assoc]
    have hmul : ((((qv v ^ w i : ℝ≥0) : ℝ≥0∞)) ^ (M + 1)) * ENNReal.ofReal ((((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) ^ (M + 1)) = 1 := by
      have := pow_index (qv v ^ w i) ha (M + 1) (M + 1) le_rfl
      simpa using this
    rw [hmul, mul_one]
  have hr : ∀ i, (((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) = ((qv v : ℝ) ^ w i)⁻¹ := fun i => by push_cast; rfl
  have hsum : ∀ s : ℕ, 1 ≤ s → ∑' i, ENNReal.ofReal ((((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) ^ s) = ENNReal.ofReal (zetaV E v s) := by
    intro s hs
    have h := hZ s hs
    simp only [hr]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h.summable, h.tsum_eq]
  refine ⟨?_, ?_⟩
  · obtain ⟨Ψ, hΨm, hΨ, hint⟩ := GlobalTheory.T.zero_block_coefficient_induction_left F E σ hσ M J hJ n hn1 hnM h₀ h₁ h₂ (Fv F v) hloc d b lam hlam.1 m m₁ m'
      hm hm₁ hm' ((latV b v).indicator 1) (measurable_one.indicator hlatM')
    rw [lintegral_indicator_one hlatM'] at hint
    set L' := m' (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v) with hL'
    have hval : ∀ i, ∀ y ∈ A i, Ψ y = (((qv v ^ w i : ℝ≥0) : ℝ≥0∞)) ^ n * L' := by
      rintro i y ⟨y₀, hy₀, rfl⟩
      obtain ⟨g, hg1, hg2⟩ := GlobalTheory.T.local_unit_scaling_lattice_measure F E σ hσ M J hJ n d b v lam hlam
        (m' (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀)) (c i) (qv v ^ w i) (c1 i).1 (c1 i).2
        (c2 i lam hlam) y₀ hy₀
      rw [← hg1, hΨ g, hg2]
    have hz : ∀ᵐ y ∂(m₁ S₁), y ∉ ⋃ i, A i → Ψ y = 0 := by
      filter_upwards [hfree, hlatE] with y hy hl hyA
      obtain ⟨g, rfl⟩ := GlobalTheory.T.local_isotropic_orbit_of_e0 F E σ hσ M J hJ v y hy.1 hy.2
      rw [hΨ g]
      exact stageInt_zero σ J b lam _ g (hl hyA)
    rw [hint, lintegral_pieces (m₁ S₁) A hAm hAd Ψ _ hval hz]
    have hterm : ∀ i, (((qv v ^ w i : ℝ≥0) : ℝ≥0∞)) ^ n * L' * m₁ S₁ (A i) =
        L' * m₁ S₁ P * ENNReal.ofReal ((((qv v ^ w i : ℝ≥0) : ℝ)⁻¹) ^ (M + 1 - n)) := by
      intro i
      have hq0 : qv v ^ w i ≠ 0 := by
        refine pow_ne_zero _ fun h0 => ?_
        have : Ideal.absNorm v.asIdeal = 0 := by simpa [qv] using h0
        exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)
      rw [e2, ← pow_index (qv v ^ w i) hq0 n (M + 1) (by omega)]
      ring
    simp only [hterm]
    rw [ENNReal.tsum_mul_left, hsum _ (by omega)]
  · rw [e1]
    simp only [e2]
    rw [ENNReal.tsum_mul_left, hsum _ (by omega)]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH

theorem qv_ge_two {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : (2 : ℝ) ≤ (qv v : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  have : (qv v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by simp [qv]
  rw [this]
  exact_mod_cast h2

theorem inv_one_sub_bounds {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 4) :
    1 ≤ (1 - u)⁻¹ ∧ (1 - u)⁻¹ ≤ 1 + 4 * u ∧ 1 ≤ ((1 - u)⁻¹) ^ 2 ∧ ((1 - u)⁻¹) ^ 2 ≤ 1 + 4 * u := by
  have hp : 0 < 1 - u := by linarith
  have hw : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ hp).2 (by linarith)
  refine ⟨hw, ?_, one_le_pow₀ hw, ?_⟩
  · rw [inv_le_iff_one_le_mul₀ hp]
    nlinarith
  · rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg h0 (sub_nonneg.2 h1)]

theorem zetaV_bounds {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (s : ℕ) (hs : 2 ≤ s) :
    1 ≤ zetaV E v s ∧ zetaV E v s ≤ 1 + 4 * (1 / (qv v : ℝ) ^ 2) := by
  have hq := qv_ge_two v
  have hq1 : (1 : ℝ) ≤ (qv v : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (qv v : ℝ) := by linarith
  have hsq : (4 : ℝ) ≤ (qv v : ℝ) ^ 2 := by nlinarith
  have hu : ∀ t : ℕ, 2 ≤ t → ((qv v : ℝ) ^ t)⁻¹ ≤ 1 / (qv v : ℝ) ^ 2 := fun t ht => by
    rw [one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hq1 ht)
  have hq4 : 1 / (qv v : ℝ) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hsq
  unfold zetaV
  split_ifs with hf
  · have h1 := hu (2 * s) (by omega)
    obtain ⟨a, b', -, -⟩ := inv_one_sub_bounds (u := ((qv v : ℝ) ^ (2 * s))⁻¹) (by positivity) (h1.trans hq4)
    exact ⟨a, b'.trans (by linarith)⟩
  · have h1 := hu s hs
    obtain ⟨-, -, a, b'⟩ := inv_one_sub_bounds (u := ((qv v : ℝ) ^ s)⁻¹) (by positivity) (h1.trans hq4)
    exact ⟨a, b'.trans (by linarith)⟩

theorem real_bound {x y p Z₁ Z₂ e : ℝ} (hy : y = p * Z₂) (hp : 0 ≤ p) (h1 : 1 ≤ Z₁) (h1' : Z₁ ≤ 1 + e)
    (h2 : 1 ≤ Z₂) (h2' : Z₂ ≤ 1 + e) (he : e ≤ 1) (hy1 : |y - 1| ≤ 1) :
    |x * p * Z₁ - 1| ≤ 4 * |x - 1| + 2 * e + |y - 1| := by
  have hy2 : y ≤ 2 := by linarith [(abs_le.1 hy1).2]
  have hp2 : p ≤ 2 := by nlinarith
  have hZ : Z₁ ≤ 2 := by linarith
  have e1 : x * p * Z₁ - 1 = (x - 1) * (p * Z₁) + p * (Z₁ - Z₂) + (y - 1) := by rw [hy]; ring
  have b1 : |(x - 1) * (p * Z₁)| ≤ 4 * |x - 1| := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ p * Z₁), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    nlinarith
  have b2 : |p * (Z₁ - Z₂)| ≤ 2 * e := by
    rw [abs_mul, abs_of_nonneg hp]
    have : |Z₁ - Z₂| ≤ e := abs_le.2 ⟨by linarith, by linarith⟩
    exact mul_le_mul hp2 this (abs_nonneg _) (by norm_num)
  rw [e1]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add b1 b2)) le_rfl)

theorem mass_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b) (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ (n + 1) → Measure (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E)) (m₁ : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) (m' : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) (n + 1) (coordW (Fv F v) b (lam v) (n + 1) (M + 2)) (coordHerm (Fv F v) σ b (lam v) (n + 1)) (m v)) → (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b (lam v) 1 (M + 2)) (coordHerm (Fv F v) σ b (lam v) 1) (m₁ v)) → (∀ v, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m' v)) → (∀ v, m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) < ⊤) → Summable (fun v => |(m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1|) → (∀ v, m' v (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v) < ⊤) → Summable (fun v => |(m' v (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v)).toReal - 1|) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v) < ⊤) ∧ Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v)).toReal - 1|) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n hn1 hnM h₀ h₁ h₂ d b lam hlam m m₁ m' hm hm₁ hm' fin₁ sum₁ fin' sum'
  have hJ' : IsHermND σ (hypOne J) := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem F E σ hσ M J hJ).1
  have fin₀ : ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁) (latV b v) < ⊤ := fun v =>
    GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH.finite_lt F E σ hσ (M + 2) (hypOne J) hJ' (n + 1) (by omega) (by omega) h₁ d b v (lam v) (hlam v) (m v) (hm v)
  refine ⟨fin₀, ?_⟩
  have hq : Summable fun v : HeightOneSpectrum (𝓞 F) => 1 / (qv v : ℝ) ^ 2 := by
    have := GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F
    simpa [qv] using this
  have hB : Summable fun v : HeightOneSpectrum (𝓞 F) =>
      4 * |(m' v (hermOf (Fv F v) σ (0 : Matrix (Fin n) (Fin n) E) h₀) (latV b v)).toReal - 1| +
        2 * (4 * (1 / (qv v : ℝ) ^ 2)) +
        |(m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1| :=
    ((sum'.mul_left 4).add ((hq.mul_left 4).mul_left 2)).add sum₁
  have hsmall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      |(m₁ v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1| < 1 :=
    sum₁.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually hB ?_
  filter_upwards [good_local F E σ hσ M J hJ n hn1 hnM h₀ h₁ h₂ d b, hsmall] with v hg hs
  obtain ⟨g1, g2⟩ := hg (lam v) (hlam v) (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v)
  obtain ⟨z1, z1'⟩ := zetaV_bounds E v (M + 1 - n) (by omega)
  obtain ⟨z2, z2'⟩ := zetaV_bounds E v (M + 1) (by omega)
  have hq2 := qv_ge_two v
  have he : 4 * (1 / (qv v : ℝ) ^ 2) ≤ 1 := by
    have h4 : (4 : ℝ) ≤ (qv v : ℝ) ^ 2 := by nlinarith
    rw [mul_one_div, div_le_one (by positivity)]
    exact h4
  rw [Real.norm_eq_abs, abs_abs, g1, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith)]
  refine real_bound ?_ ENNReal.toReal_nonneg z1 z1' z2 z2' he hs.le
  rw [g2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.HH
