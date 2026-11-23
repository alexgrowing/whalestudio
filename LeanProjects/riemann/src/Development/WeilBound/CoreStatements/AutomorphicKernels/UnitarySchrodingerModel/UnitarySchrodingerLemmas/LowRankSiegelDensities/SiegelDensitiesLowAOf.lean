import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.Reduce
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocalDensitiesConverges
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddBlockAnisotropic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfRankSmallOrZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteVolumeInductionCompactSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PfSWUS.HMass

def IsAnisoH {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Prop :=
  ∀ x : Fin M → E, x ≠ 0 → hE σ J x x ≠ 0

def OneVecBinary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → M = 2 → IsAnisoH σ J →
  ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT

def OneVecBinaryMass : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → M = 2 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∃ C : ℝ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (lam : Measure (Fv F v)), IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m →
      ∀ s : Fv F v, Valued.v s = 1 →
        |(m (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isAnisoH_of_isometry (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E)
    (hJ : IsAnisoH σ J) : IsAnisoH σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) := by
  intro x hx
  rw [← GlobalTheory.CompanionTheory.SW.CountGen.hE_mulVec]
  apply hJ
  intro h0
  apply hx
  have := congrArg (fun y => ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ y) h0
  simpa [Matrix.mulVec_mulVec] using this

theorem hE_block_cons (σ : E →ₐ[F] E) {M : ℕ} (c : E) (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    hE σ (blockOne c J) (Fin.cons 0 x) (Fin.cons 0 x) = hE σ J x x := by
  simp [hE, hform, blockOne, Fin.sum_univ_succ]

theorem isAnisoH_of_block (σ : E →ₐ[F] E) {M : ℕ} (c : E) (J : Matrix (Fin M) (Fin M) E)
    (h : IsAnisoH σ (blockOne c J)) : IsAnisoH σ J := by
  intro x hx
  rw [← hE_block_cons σ c J x]
  apply h
  intro h0
  apply hx
  funext i
  simpa using congrFun h0 i.succ

end Alg

theorem arith2 {x y q A B : ℝ} (hq : 1 ≤ q) (hx : |x - 1| ≤ A / q ^ 2) (hy : |y - 1| ≤ B / q ^ 2) :
    |x * y - 1| ≤ (|A| + |B| + |A| * |B|) / q ^ 2 := by
  have hq0 : 0 < q ^ 2 := by positivity
  set e : ℝ := 1 / q ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one hq0]
    nlinarith
  have hx' : |x - 1| ≤ |A| * e := by
    refine hx.trans ?_
    rw [he, mul_one_div]
    exact div_le_div_of_nonneg_right (le_abs_self A) hq0.le
  have hy' : |y - 1| ≤ |B| * e := by
    refine hy.trans ?_
    rw [he, mul_one_div]
    exact div_le_div_of_nonneg_right (le_abs_self B) hq0.le
  have hA : 0 ≤ |A| := abs_nonneg A
  have hB : 0 ≤ |B| := abs_nonneg B
  have hdec : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  have hprod : |(x - 1) * (y - 1)| ≤ |A| * |B| * e := by
    rw [abs_mul]
    calc |x - 1| * |y - 1| ≤ (|A| * e) * (|B| * e) :=
          mul_le_mul hx' hy' (abs_nonneg _) (by positivity)
      _ = |A| * |B| * e * e := by ring
      _ ≤ |A| * |B| * e * 1 := mul_le_mul_of_nonneg_left he1 (by positivity)
      _ = |A| * |B| * e := by ring
  have htri : |x * y - 1| ≤ |(x - 1) * (y - 1)| + |x - 1| + |y - 1| := by
    rw [hdec]
    exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hfin : (|A| + |B| + |A| * |B|) / q ^ 2 = (|A| + |B| + |A| * |B|) * e := by rw [he, mul_one_div]
  rw [hfin]
  nlinarith

theorem one_vec_sw (hE1 : OneVecBinary) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    2 ≤ M → (3 ≤ M ∨ IsAnisoH σ J) → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → SWMeas σ J T hT := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM ha T hT hd
  by_cases h : 3 ≤ M
  · exact GlobalTheory.T.siegel_weil_measure_rank_one F E σ hCM M J hJ h T hT hd
  · exact hE1 F E σ hCM M J hJ (by omega) (ha.resolve_left h) T hT hd

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open GlobalTheory.CompanionTheory.SW.GoodMass

theorem one_vec_bound (hE2 : OneVecBinaryMass) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (hM : 2 ≤ M) {d : ℕ} (b : Module.Basis (Fin d) F E) : ∃ C : ℝ,
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (lam : Measure (Fv F v)), IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m →
      ∀ s : Fv F v, Valued.v s = 1 →
        |(m (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  by_cases h : 3 ≤ M
  · refine ⟨2, ?_⟩
    filter_upwards [GlobalTheory.T.rank_one_local_density_almost_all F E σ hcm M J hJ h d b] with v hv lam hl m hm s hs
    have hint : s ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hs.le
    have hne : s ≠ 0 := by
      intro h0
      rw [h0] at hs
      simp at hs
    refine (hv lam hl m hm s hint hne).trans ?_
    have hq := absNorm_one_le (F := F) v
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ hq (by omega))
  · exact hE2 F E σ hcm M J hJ (by omega) d b

theorem mass_good_lt (hE2 : OneVecBinaryMass) (hcm : IsCMExt F E σ) : ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    n < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
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
    obtain ⟨C₁, hC₁⟩ := ih M₁ 1 hone (by omega) T₁ hT₁.1 hT₁.2 d b
    obtain ⟨C₀, hC₀⟩ := one_vec_bound hE2 hcm (M₁ + 1) _ hJ' (by omega) b
    refine ⟨|C₀| + |C₁| + |C₀| * |C₁|, ?_⟩
    have e1 := GlobalTheory.T.local_densities_congruent_target_almost_all F E σ hcm (M₁ + 1) J hJ (n + 1) T hT hdet g hgdet _ hbh hblock d b
    have e2 := GlobalTheory.T.local_gram_fiber_measures_agree_almost_all F E σ hcm (M₁ + 1) J hJ _ hJ' d b (n + 1)
    have e3 := GlobalTheory.T.local_densities_block_one_almost_all F E σ hcm M₁ 1 hone t ht n T₁ hT₁.1 hT₁.2 hbh d b
    have e5 := (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 t ht
    filter_upwards [e1, e2, e3, hC₀, e5, hC₁] with v h1 h2 h3 h4 h5 h6 lam hl m hm
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
    have a4 := h4 lam hl m₁ hm₁ _ h5
    have a6 := h6 lam hl m₂ hm₂
    rw [← a1, a2, a3, ENNReal.toReal_mul]
    exact arith2 (absNorm_one_le v) a4 a6

end Main

theorem mass_summable_lt (hE2 : OneVecBinaryMass) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → (∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn T hT hdet d b lam hlam m hm
  refine ⟨?_, ?_⟩
  · intro v
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh.2.1 n M
    haveI hH := hh.2.2 n
    have hlf := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Fv F v) hloc n _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b n M v).1.measure_lt_top
  · obtain ⟨C, hC⟩ := mass_good_lt hE2 hCM n M J hJ hn T hT hdet d b
    refine Summable.of_norm_bounded_eventually
      (g := fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
      ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C) ?_
    filter_upwards [hC] with v hv
    have := hv (lam v) (hlam v) (m v) (hm v)
    rw [Real.norm_eq_abs, abs_abs]
    simpa [div_eq_mul_inv] using this

theorem notRep_lt (hE1 : OneVecBinary) (hE2 : OneVecBinaryMass) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → (3 ≤ M ∨ IsAnisoH σ J) → ∀ n : ℕ, n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), (∀ x : Fin M → E, hE σ J x x ≠ algebraMap F E t) → SWMeas σ J (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht hA n hn T hT hdet hT' hne
  intro d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf m hminf hm
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hLinf : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  have haarOf : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
      [BorelSpace R], IsLocR R → ∀ lam' : Measure R, lam'.IsAddHaarMeasure →
      (∀ n' M' : ℕ, (coordW R b lam' n' M').IsAddHaarMeasure) ∧
        ∀ n' : ℕ, (coordHerm R σ b lam' n').IsAddHaarMeasure := by
    intro R _ _ _ _ _ hLoc lam' hl
    obtain ⟨_, _, _, _, -⟩ := hLoc
    exact (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam' hl).2
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun _ _ => σ.commutes t
  have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
  have hdet1 : T1.det ≠ 0 := by
    rw [Matrix.det_fin_one]; exact htE
  have hsw := one_vec_sw hE1 F E σ hCM M J hJ (by omega) hA T1 hT1 hdet1
  obtain ⟨minf1, hminf1⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ (Ainf F) hLinf 1 _ _
    ((haarOf _ hLinf laminf hinf.1).1 1 M) ((haarOf _ hLinf laminf hinf.1).2 1)
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m' : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) m' :=
    fun v => GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ (Fv F v) (hLv v) 1 _ _
      ((haarOf _ (hLv v) (lam v) (hv v).1).1 1 M) ((haarOf _ (hLv v) (lam v) (hv v).1).2 1)
  choose m1 hm1 using hex
  have hEul := hsw d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf1 m1 hminf1 hm1
  have hS1 : {X : Fin 1 → Fin M → E | gramE σ J X = T1} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    exact hne (X 0) (congrFun (congrFun hX 0) 0)
  have hS : {X : Fin (n + 1) → Fin M → E | gramE σ J X = blockOne (algebraMap F E t) T} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    apply hne (X 0)
    simpa [gramE, blockOne] using congrFun (congrFun hX 0) 0
  have hz := ((GlobalTheory.T.euler_product_measure_zero F E σ hCM d b 1 M _ 1 _ _).1 hEul
    (SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS1))
  have hvan : minf (hermOf (Ainf F) σ (blockOne (algebraMap F E t) T) hT') = 0 ∨
      ∃ v, m v (hermOf (Fv F v) σ (blockOne (algebraMap F E t) T) hT') = 0 := by
    rcases hz with h | h | ⟨v, h⟩
    · exact absurd h one_ne_zero
    · exact Or.inl (SwEmpty.fibre_zero_of_one σ hCM J hJ (Ainf F) hLinf b laminf hinf.1 t ht T hT' T1 rfl hT1
        minf1 minf hminf1 hminf h)
    · exact Or.inr ⟨v, SwEmpty.fibre_zero_of_one σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hv v).1 t ht T hT' T1 rfl hT1
        (m1 v) (m v) (hm1 v) (hm v) h⟩
  have hdetB : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [((GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM n T t).1)]
    exact mul_ne_zero htE hdet
  obtain ⟨hfin, hsum⟩ := mass_summable_lt hE2 F E σ hCM M J hJ (n + 1) (by omega)
    (blockOne (algebraMap F E t) T) hT' hdetB d b lam (fun v => hv v) m hm
  rw [SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS]
  exact (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b (n + 1) M 0 1 _ _).2.2 hfin hsum hvan

theorem step_lt (hE1 : OneVecBinary) (hE2 : OneVecBinaryMass) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → (2 ≤ M ∨ IsAnisoH σ (blockOne (algebraMap F E t) J)) → ∀ n : ℕ, n + 1 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), SWMeas σ J T hT → SWMeas σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht hA n hn T hT hdet hT' hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩
  have hdet' : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [(GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM n T t).1]; exact mul_ne_zero hta hdet

  obtain ⟨m₁inf, hm₁inf⟩ := Step.loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := Step.loc_families σ hCM J hJ (Ainf F) hLi b laminf hinf.1 n
  choose m₁ hm₁ using fun v => Step.loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1
  choose m' hm' using fun v => Step.loc_families σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hlam v).1 n
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁

  obtain ⟨cinf, c, hc, hcinf, hcv⟩ := GlobalTheory.T.scalar_multiplication_euler_product F E σ hCM (algebraMap F E t) hta
  have hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) =
      cinf • coordK (Ainf F) b laminf := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLi
    exact hcinf _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1).1
  have hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      c v • coordK (Fv F v) b (lam v) := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    exact hcv v _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1
  obtain ⟨-, -, -, -, -, -, -, S₃, hS₃⟩ := GlobalTheory.T.unit_product_closure_properties F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩

  have hE' := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf (fun v => m' v) hm'inf hm'
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun a b => by simp [T1]
  have hdet1 : T1.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hta
  have hE₁ := one_vec_sw hE1 F E σ hCM (M + 1) _ hJ' (by omega) (hA.imp_left (by omega)) T1 hT1 hdet1 d b laminf lam hinf hlam μ 𝓕 hμ h𝓕
    m₁inf m₁ hm₁inf hm₁
  obtain ⟨β, hβ1, -, hβ2⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hCM T1 hT1
  have hβ : β = t := (algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm
  rw [hβ] at hβ2
  simp only [hβ2] at hE₁
  obtain ⟨-, hsum₁, S₁, hS₁⟩ := hE₁
  have hsum' := hE'.2.1
  have hgood := mass_summable_lt hE2 F E σ hCM (M + 1) _ hJ' (n + 1) (by omega) _ hT' hdet' d b lam hlam m hm
  refine ⟨hgood.1, hgood.2, ?_⟩
  obtain ⟨S₂, hS₂⟩ := Step.theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'
  have hG := GlobalTheory.T.local_density_block_one_eventually F E σ hCM M J hJ t ht n T hT hdet hT' d b
  have hSG := GlobalTheory.T.local_measures_orthogonal_sum_almost_all_places F E σ hCM M J hJ t ht n T hT hdet d b
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset,
    fun S hS φinf φ hφinf hφ => ?_⟩
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hx))
  have hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inr hx)
  obtain ⟨hc1, hc2⟩ := hS₃ S hS3
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 n M, hh.2.2 n⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    Step.of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ) := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm
  have hth := GlobalTheory.T.lintegral_thetaMeas_block_one_eq_rank_one F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
    (fun y => τ' * pureL b S Ψinf Ψ y) (GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (n + 1) (M + 1) S φinf φ hφinf hφ)
    (hPm.const_mul τ') hHyp
  have hone := hS₁ S hS1 Ψinf Ψ hΨinfm hΨm
  rw [hth, lintegral_const_mul _ hPm]
  have hone' : ∫⁻ X, pureL b S Ψinf Ψ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _ := hone
  rw [hone']
  have hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ _ hT')) =
      (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    have hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hc2
    rw [hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) ^ n * ((∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))) := by rw [mul_pow]; ring
      _ = _ := by rw [hone2, one_pow, one_mul]
  have htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal) =
      τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) := by
    have hA := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal)
      (hsum'.subtype _)
    have hB := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)
      (hsum₁.subtype _)
    have hcong : ∀ v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal =
        (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal * (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal := fun v => by
      rw [Step.of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

theorem swMeas_lt (hE1 : OneVecBinary) (hE2 : OneVecBinaryMass) : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ)
    (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → n < M → (n + 2 ≤ M ∨ IsAnisoH σ J) →
    ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro M J hJ _ _ T hT hd
    exact GlobalTheory.T.siegel_weil_measure_rank_zero F E σ hσ M J hJ T hT hd
  | succ n ih =>
    intro M J hJ hn hR T hT hd
    by_cases hbig : n + 1 + 2 ≤ M
    · exact GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero F E σ hσ (n + 1) M J hJ (Or.inr hbig) T hT hd
    have ha : IsAnisoH σ J := hR.resolve_left hbig
    have hM : n + 2 ≤ M := by omega
    obtain ⟨t, x, ht, hx⟩ := GlobalTheory.CompanionTheory.SW.HermRep.exists_repr F E σ hσ n T ⟨hT, hd⟩
    obtain ⟨g, T₁, hT₁, hb, -⟩ :=
      GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ n T ⟨hT, hd⟩ t x ht hx
    obtain ⟨hdet, hblk, -, -⟩ := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hσ n T₁ t
    have hT' := hblk hT₁.1
    have htE : algebraMap F E t ≠ 0 := by
      simpa using ht
    have hd' : (blockOne (algebraMap F E t) T₁).det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero htE hT₁.2
    refine GlobalTheory.T.siegel_weil_measure_of_congruent_target F E σ hσ M J hJ (n + 1) T hT hd g _ hT' hb ?_
    by_cases hrep : ∃ y : Fin M → E, hE σ J y y = algebraMap F E t
    · obtain ⟨y, hy⟩ := hrep
      obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 1 := ⟨M - 1, by omega⟩
      obtain ⟨g', J₁, hJ₁, hb', -⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ M₁ J hJ t y ht hy
      have ha' : IsAnisoH σ (blockOne (algebraMap F E t) J₁) := by
        rw [hb']
        exact isAnisoH_of_isometry σ J g' ha
      refine GlobalTheory.T.siegel_weil_measure_of_congruent_form F E σ hσ (M₁ + 1) J hJ g' _ hb' (n + 1) _ hT' hd' ?_
      exact step_lt hE1 hE2 F E σ hσ M₁ J₁ hJ₁ t ht (Or.inr ha') n (by omega) T₁ hT₁.1 hT₁.2 hT'
        (ih M₁ J₁ hJ₁ (by omega) (Or.inr (isAnisoH_of_block σ _ J₁ ha')) T₁ hT₁.1 hT₁.2)
    · exact notRep_lt hE1 hE2 F E σ hσ M J hJ t ht (Or.inr ha) n hM T₁ hT₁.1 hT₁.2 hT'
        (fun y hy => hrep ⟨y, hy⟩)

def SiegelDensitiesLowA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (n : ℕ), n < M → (n + 2 ≤ M ∨ IsAnisoH σ J) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    PositivityTheory.PfSWUS.Loc.IsSchwartzInf Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)

theorem siegelDensitiesLowA_of (hE1 : OneVecBinary) (hE2 : OneVecBinaryMass) (hB : SchwartzDensInf) :
    SiegelDensitiesLowA := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn hR T hT hdet d b Φ Φinf Φf Φv hsch hpure hprod
  have hfv : FinVol F E σ M J := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  refine ⟨hfv.1, fun μ hμ => ⟨(hfv.2 μ hμ).1, fun 𝓕 h𝓕 =>
    ⟨GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F, fun ψ hψ => ?_⟩⟩⟩
  obtain ⟨⟨laminf, hli⟩, hlv⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlv
  obtain ⟨ci, c, hc1, hWi, hWv⟩ := GlobalTheory.T.exists_unit_scaling_selfdual_adelic_measures F E σ hCM M J hJ d b laminf lam hli hlam ψ hψ n
  obtain ⟨ei, e, he1, hHi, hHv⟩ := GlobalTheory.T.exists_unit_scaling_selfdual_herm_measures F E σ hCM d b laminf lam hli hlam ψ hψ n
  obtain ⟨hci0, hc0, -, -, hdiv, -⟩ := GlobalTheory.T.unit_product_closure_properties F ci ei c e hc1 he1
  obtain ⟨hei0, he0, -⟩ := GlobalTheory.T.unit_product_closure_properties F ei ci e c he1 hc1
  refine ⟨⟨_, (hWi _).2 rfl⟩, fun μinf hμinf => ⟨⟨_, (hHi _).2 rfl⟩, fun νinf hνinf =>
    ⟨⟨_, fun v => (hWv v _).2 rfl⟩, fun μv hμv => ⟨⟨_, fun v => (hHv v _).2 rfl⟩, fun νv hνv => ?_⟩⟩⟩⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have key : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R],
      IsLocR R → ∀ l : Measure R, l.IsAddHaarMeasure →
      ∃ m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E),
        IsGramFib R σ J n (coordW R b l n M) (coordHerm R σ b l n) m ∧ (∀ S, IsLocallyFiniteMeasure (m S)) ∧
        ∀ (a a' : ℝ≥0), a ≠ 0 → a' ≠ 0 → (a • coordW R b l n M).IsAddHaarMeasure →
          (a' • coordHerm R σ b l n).IsAddHaarMeasure →
          ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℂ, Continuous φ → HasCompactSupport φ →
          IsContDensityOn (a • coordW R b l n M) (gramR R σ J) Subtype.val (a' • coordHerm R σ b l n)
            {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} φ
            (fun S => (a / a') • ∫ X, φ X ∂(m S)) := by
    intro R _ _ _ _ _ hR l hl
    obtain ⟨i1, i2, i3, i4, -⟩ := id hR
    obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b l hl
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ R hR n _ _ (hW n M) (hH n)
    refine ⟨m, hm, fun S => (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ R hR n _ _ m (hW n M) (hH n) hm S).1, ?_⟩
    intro a a' ha ha' h1 h2 φ hφ hφc
    have h3 := GlobalTheory.T.gram_fiber_measures_scaling F E σ hCM M J hJ R hR n _ _ m (hW n M) (hH n) hm a a' ha ha'
    have h4 := (GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ hCM M J hJ R hR n _ _ _ h1 h2 h3 φ hφ hφc).1
    simpa only [integral_smul_nnreal_measure] using h4
  have keyi : ∃ m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E),
      IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) m ∧
      (∀ S, IsLocallyFiniteMeasure (m S)) ∧ Continuous Φinf ∧
      (∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable Φinf (m S)) ∧
      ∀ (a a' : ℝ≥0), a ≠ 0 → a' ≠ 0 → (a • coordW (Ainf F) b laminf n M).IsAddHaarMeasure →
        (a' • coordHerm (Ainf F) σ b laminf n).IsAddHaarMeasure →
        IsContDensityOn (a • coordW (Ainf F) b laminf n M) (gramR (Ainf F) σ J) Subtype.val
          (a' • coordHerm (Ainf F) σ b laminf n)
          {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf
          (fun S => (a / a') • ∫ X, Φinf X ∂(m S)) := by
    obtain ⟨i1, i2, i3, i4, -⟩ := id hLi
    obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hli.1
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ (Ainf F) hLi n _ _ (hW n M) (hH n)
    obtain ⟨hcI, -, hiI⟩ := hB F E σ hCM M J hJ n _ _ m (hW n M) (hH n) hm Φinf hsch
    refine ⟨m, hm, fun S => (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Ainf F) hLi n _ _ m (hW n M) (hH n) hm S).1,
      hcI, hiI, ?_⟩
    intro a a' ha ha' h1 h2
    have h3 := GlobalTheory.T.gram_fiber_measures_scaling F E σ hCM M J hJ (Ainf F) hLi n _ _ m (hW n M) (hH n) hm a a' ha ha'
    have h4 := (hB F E σ hCM M J hJ n _ _ _ h1 h2 h3 Φinf hsch).2.1
    simpa only [integral_smul_nnreal_measure] using h4
  obtain ⟨minf, hmi, hfi, hcI, hiI, hdi⟩ := keyi
  choose m hm hf hd using fun v => key (Fv F v) (hLv v) (lam v) (hlam v).1
  have e1 := (hWi μinf).1 hμinf
  have e2 := (hHi νinf).1 hνinf
  have e3 := fun v => (hWv v (μv v)).1 (hμv v)
  have e4 := fun v => (hHv v (νv v)).1 (hνv v)
  have hSW : SWMeas σ J T hT := swMeas_lt hE1 hE2 F E σ hCM n M J hJ hn hR T hT hdet
  have hE := hSW d b laminf lam hli hlam μ 𝓕 hμ h𝓕 minf m hmi hm
  obtain ⟨hmeas, hint, hmul, hI⟩ := euler_int_integrable F E σ hCM d b n M _ _ _ hE (hfi _) (fun v => hf v _)
    Φ Φinf Φf Φv hcI (hiI _ (isUnit_det_hermOf (Ainf F) σ T hT hdet)) hpure hprod
  have hθ := GlobalTheory.T.siegel_mean_value_integrable F E σ hCM M J hJ μ 𝓕 hμ h𝓕 n _ Φ hmeas hint
  obtain ⟨r1, r2⟩ := GlobalTheory.CompanionTheory.SW.TopDens.rescale_tprod (ci / ei) (fun v => c v / e v) hdiv.1 hdiv.2
    (∫ X, Φinf X ∂(minf (hermOf (Ainf F) σ T hT))) _ hmul
  refine ⟨fun S => (ci / ei) • ∫ X, Φinf X ∂(minf S), fun v S => (c v / e v) • ∫ X, Φv v X ∂(m v S),
    ?_, fun v => ?_, r1, ?_⟩
  · have := hdi ci ei hci0 hei0 (e1 ▸ hμinf.1) (e2 ▸ hνinf.1)
    rwa [← e1, ← e2] at this
  · have := hd v (c v) (e v) (hc0 v) (he0 v) (e3 v ▸ (hμv v).1) (e4 v ▸ (hνv v).1) (Φv v)
      (hpure.1 v).1.continuous (hpure.1 v).2
    rwa [← e3 v, ← e4 v] at this
  · rw [hθ, hI]
    exact r2.symm

theorem swMeas_edge_aniso (hE1 : OneVecBinary) (hE2 : OneVecBinaryMass) : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ J → IsAnisoH σ J →
    ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT :=
  fun F E _ _ _ _ _ σ hσ n J hJ ha T hT hd => swMeas_lt hE1 hE2 F E σ hσ n (n + 1) J hJ (by omega) (Or.inr ha) T hT hd

end PositivityTheory.PfSWUS.HMass
