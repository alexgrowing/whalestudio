import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberMeasuresAgreeAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesCongruentTargetAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBlockOneAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankZeroGramFiberMeasureStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodMass

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_moved (hcm : IsCMExt F E σ) : ∃ c : E, σ c ≠ c := by
  by_contra h
  push_neg at h
  obtain ⟨-, htc, -, hconj⟩ := hcm
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc : w.IsComplex := htc.isComplex w
  have hr : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    have := hconj w.embedding x
    rw [h x] at this
    simp only [ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 hc hr

theorem fixed_mem (hcm : IsCMExt F E σ) (x : E) (hx : σ x = x) : ∃ t : F, algebraMap F E t = x := by
  obtain ⟨c, hc⟩ := exists_moved hcm
  have hfr : Module.finrank F E = 2 := hcm.2.2.1
  haveI : IsSimpleOrder (Subalgebra F E) :=
    Subalgebra.isSimpleOrder_of_finrank_prime F E (by rw [hfr]; exact Nat.prime_two)
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
  · have hm : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := by
      simpa [AlgHom.mem_equalizer] using hx
    rw [h, Algebra.mem_bot] at hm
    exact hm
  · have hm : c ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
    exact absurd (by simpa [AlgHom.mem_equalizer] using hm) hc

theorem hE_add_left {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hE σ T (x + x') y = hE σ T x y + hE σ T x' y := by
  simp [hE, hform, add_mul, Finset.sum_add_distrib]

theorem hE_add_right {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    hE σ T x (y + y') = hE σ T x y + hE σ T x y' := by
  simp [hE, hform, mul_add, Finset.sum_add_distrib]

theorem hE_smul_left {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    hE σ T (c • x) y = σ c * hE σ T x y := by
  simp [hE, hform, Finset.mul_sum, mul_assoc]

theorem hE_smul_right {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    hE σ T x (c • y) = c * hE σ T x y := by
  simp only [hE, hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_single {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hE σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  simp [hE, hform, Pi.single_apply]

theorem hE_self_fixed {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (x : Fin n → E) (hinv : ∀ y, σ (σ y) = y) : σ (hE σ T x x) = hE σ T x x := by
  simp only [hE, hform, map_sum, map_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hinv, hT]
  ring

end Alg

section Alg2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_aniso (hcm : IsCMExt F E σ) {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) :
    ∃ (x : Fin (n + 1) → E) (t : F), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by
  by_contra hno
  push_neg at hno
  have hinv : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    apply w.embedding.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have h1 : ∀ x, hE σ T x x = 0 := by
    intro x
    obtain ⟨t, ht⟩ := fixed_mem hcm _ (hE_self_fixed T hT x hinv)
    by_cases h0 : t = 0
    · rw [← ht, h0, map_zero]
    · exact absurd ht.symm (hno x t h0)
  have h2 : ∀ x y, hE σ T x y + hE σ T y x = 0 := by
    intro x y
    have := h1 (x + y)
    rw [hE_add_left, hE_add_right, hE_add_right, h1 x, h1 y] at this
    linear_combination this
  obtain ⟨c, hc⟩ := exists_moved hcm
  have h3 : ∀ x y, hE σ T x y = 0 := by
    intro x y
    have e := h2 (c • x) y
    rw [hE_smul_left, hE_smul_right] at e
    have e' : (σ c - c) * hE σ T x y = 0 := by
      linear_combination e - c * h2 x y
    exact (mul_eq_zero.1 e').resolve_left (sub_ne_zero.2 hc)
  apply hdet
  have hz : T = 0 := by
    ext i j
    rw [← hE_single (σ := σ) T i j, h3]
    rfl
  rw [hz, Matrix.det_zero]

theorem blockOne_herm {M : ℕ} (a : E) (ha : σ a = a) (A : Matrix (Fin M) (Fin M) E)
    (hA : ∀ i j, σ (A j i) = A i j) : ∀ i j, σ (blockOne a A j i) = blockOne a A i j := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simpa [blockOne] using ha
  · simp [blockOne]
  · simp [blockOne]
  · simpa [blockOne] using hA i' j'

theorem one_hermND (M : ℕ) : IsHermND σ (1 : Matrix (Fin M) (Fin M) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem blockOne_hermND {M : ℕ} (t : F) (ht : t ≠ 0) :
    IsHermND σ (blockOne (algebraMap F E t) (1 : Matrix (Fin M) (Fin M) E)) := by
  refine ⟨blockOne_herm _ (σ.commutes t) _ (one_hermND M).1, ?_⟩
  rw [AlgSplit.det_blockOne]
  simpa using ht

end Alg2

theorem arith {x y q C : ℝ} {k : ℕ} (hq : 1 ≤ q) (hk : 2 ≤ k) (hx : |x - 1| ≤ 2 / q ^ k)
    (hy : |y - 1| ≤ C / q ^ 2) : |x * y - 1| ≤ (3 * |C| + 2) / q ^ 2 := by
  have hq0 : 0 < q ^ 2 := by positivity
  set e : ℝ := 1 / q ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one hq0]
    nlinarith
  have hx' : |x - 1| ≤ 2 * e := by
    refine hx.trans ?_
    rw [he, mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) hq0 (pow_le_pow_right₀ hq hk)
  have hy' : |y - 1| ≤ |C| * e := by
    refine hy.trans ?_
    rw [he, mul_one_div]
    exact div_le_div_of_nonneg_right (le_abs_self C) hq0.le
  have hC : 0 ≤ |C| := abs_nonneg C
  have hdec : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  have hprod : |(x - 1) * (y - 1)| ≤ 2 * |C| * e := by
    rw [abs_mul]
    calc |x - 1| * |y - 1| ≤ (2 * e) * (|C| * e) :=
          mul_le_mul hx' hy' (abs_nonneg _) (by positivity)
      _ = 2 * |C| * e * e := by ring
      _ ≤ 2 * |C| * e * 1 := by
          exact mul_le_mul_of_nonneg_left he1 (by positivity)
      _ = 2 * |C| * e := by ring
  have htri : |x * y - 1| ≤ |(x - 1) * (y - 1)| + |x - 1| + |y - 1| := by
    rw [hdec]
    exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hfin : (3 * |C| + 2) / q ^ 2 = (3 * |C| + 2) * e := by rw [he, mul_one_div]
  rw [hfin]
  nlinarith

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_family (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hl : IsStdV v lam) (n : ℕ) :
    ∃ m, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨h1, h2, h3, h4, -⟩ := hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := hl.1
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b lam hl.1
  haveI := hW n M
  haveI := hH n
  exact GlobalTheory.T.exists_gram_fiber_measures F E σ hcm M J hJ (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) n _ _ (hW n M) (hH n)

theorem absNorm_one_le (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  exact_mod_cast this

theorem key (hcm : IsCMExt F E σ) : ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (n = 0 ∨ n + 2 ≤ M) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m →
      |(m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤
        C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro M J hJ _ T hT _ d b
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro v lam hl m hm
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have h0 := GlobalTheory.T.rank_zero_gram_fiber_measure F E σ hcm M J hJ (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) d b lam hl.1 m hm
      (hermOf (Fv F v) σ T hT)
    have hU : (latV b v : Set (Fin 0 → Fin M → Fv F v ⊗[F] E)) = Set.univ := by
      ext Y
      simp [latV]
    rw [h0, hU, measure_univ]
    simp
  | succ n ih =>
    intro M J hJ hn T hT hdet d b
    have hM : n + 3 ≤ M := by omega
    obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 1 := ⟨M - 1, by omega⟩
    obtain ⟨x, t, ht, hx⟩ := exists_aniso hcm T hT hdet
    obtain ⟨g, T₁, hT₁, hblock, -⟩ :=
      AlgSplit.split_anisotropic F E σ hcm n T ⟨hT, hdet⟩ t x ht hx
    have hbh : ∀ a b, σ (blockOne (algebraMap F E t) T₁ b a) = blockOne (algebraMap F E t) T₁ a b :=
      blockOne_herm _ (σ.commutes t) _ hT₁.1
    have hgdet : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    have hone : IsHermND σ (1 : Matrix (Fin M₁) (Fin M₁) E) := one_hermND M₁
    have hJ' : IsHermND σ (blockOne (algebraMap F E t) (1 : Matrix (Fin M₁) (Fin M₁) E)) :=
      blockOne_hermND t ht
    obtain ⟨C₁, hC₁⟩ := ih M₁ 1 hone (Or.inr (by omega)) T₁ hT₁.1 hT₁.2 d b
    refine ⟨3 * |C₁| + 2, ?_⟩
    have e1 := GlobalTheory.T.local_densities_congruent_target_almost_all F E σ hcm (M₁ + 1) J hJ (n + 1) T hT hdet g hgdet _ hbh hblock d b
    have e2 := GlobalTheory.T.local_gram_fiber_measures_agree_almost_all F E σ hcm (M₁ + 1) J hJ _ hJ' d b (n + 1)
    have e3 := GlobalTheory.T.local_densities_block_one_almost_all F E σ hcm M₁ 1 hone t ht n T₁ hT₁.1 hT₁.2 hbh d b
    have e4 := GlobalTheory.T.rank_one_local_density_almost_all F E σ hcm (M₁ + 1) _ hJ' (by omega) d b
    have e5 := (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 t ht
    filter_upwards [e1, e2, e3, e4, e5, hC₁] with v h1 h2 h3 h4 h5 h6 lam hl m hm
    obtain ⟨m', hm'⟩ := exists_family hcm hJ' b v lam hl (n + 1)
    obtain ⟨m₁, hm₁⟩ := exists_family hcm hJ' b v lam hl 1
    obtain ⟨m₂, hm₂⟩ := exists_family hcm hone b v lam hl n
    have a1 := h1 lam hl m hm
    have a2 := h2 lam hl m m' hm hm' (hermOf (Fv F v) σ _ hbh)
    have a3 := h3 lam hl m' m₁ m₂ hm' hm₁ hm₂
    have hint : algebraMap F (Fv F v) t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact h5.le
    have hne : algebraMap F (Fv F v) t ≠ 0 := by
      intro h0
      rw [h0] at h5
      simp at h5
    have a4 := h4 lam hl m₁ hm₁ _ hint hne
    have a6 := h6 lam hl m₂ hm₂
    rw [← a1, a2, a3, ENNReal.toReal_mul]
    exact arith (absNorm_one_le v) (by omega) a4 a6

end Main

theorem mass_fibre_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → |(m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro F E _ _ _ _ _ σ hcm M J hJ n hn T hT hdet d b
  exact key hcm n M J hJ hn T hT hdet d b

end GlobalTheory.CompanionTheory.SW.GoodMass
