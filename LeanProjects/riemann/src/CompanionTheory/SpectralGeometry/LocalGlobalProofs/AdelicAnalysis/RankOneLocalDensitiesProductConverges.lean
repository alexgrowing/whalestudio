import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPowerStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.LocalMassSeries.HermitianRankOneLocalVolumeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Growth

section Place
variable {F : Type} [Field F] [NumberField F]

theorem val_alg (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem val_lt_one_of_mem (v : HeightOneSpectrum (𝓞 F)) {r : 𝓞 F} (h : r ∈ v.asIdeal) :
    Valued.v ((algebraMap F (Fv F v)) (algebraMap (𝓞 F) F r)) < 1 := by
  rw [val_alg]
  exact (v.valuation_lt_one_iff_mem r).2 h

theorem val_le_one (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v ((algebraMap F (Fv F v)) (algebraMap (𝓞 F) F r)) ≤ 1 := by
  rw [val_alg]
  exact v.valuation_le_one r

theorem val_eq_one (v : HeightOneSpectrum (𝓞 F)) {r : 𝓞 F} (h : r ∉ v.asIdeal) :
    Valued.v ((algebraMap F (Fv F v)) (algebraMap (𝓞 F) F r)) = 1 := by
  refine le_antisymm (val_le_one v r) (not_lt.1 fun h' => h ?_)
  rw [val_alg] at h'
  exact (v.valuation_lt_one_iff_mem r).1 h'

theorem two_le_norm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem exists_nat_mul_mem (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    ∃ n : ℕ, 0 < n ∧ (n : Fv F v) * x ∈ v.adicCompletionIntegers F := by
  set q : 𝓞 F := ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) with hq
  have hqm : q ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hlt := val_lt_one_of_mem v hqm
  have hcast : (algebraMap F (Fv F v)) (algebraMap (𝓞 F) F q) = ((Ideal.absNorm v.asIdeal : ℕ) : Fv F v) := by
    simp [hq]
  rw [hcast] at hlt
  set y : Fv F v := ((Ideal.absNorm v.asIdeal : ℕ) : Fv F v) with hy
  have hy0 : y ≠ 0 := by
    have hq0 : q ≠ 0 := by
      rw [hq]; exact_mod_cast (by have := two_le_norm v; omega : Ideal.absNorm v.asIdeal ≠ 0)
    rw [← hcast]
    exact (map_ne_zero _).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 hq0)
  have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hgt : 1 < (Valued.v y)⁻¹ := by
    exact (one_lt_inv₀ (zero_lt_iff.2 hv0)).2 hlt
  obtain ⟨j, hj⟩ := MulArchimedean.arch (Valued.v x) hgt
  refine ⟨Ideal.absNorm v.asIdeal ^ j, pow_pos (by have := two_le_norm v; omega) j, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  push_cast
  rw [map_mul, map_pow, ← hy]
  calc Valued.v y ^ j * Valued.v x ≤ Valued.v y ^ j * (Valued.v y)⁻¹ ^ j := by gcongr
    _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hv0, one_pow]

theorem exists_exponents (a : ℕ) (ha : 0 < a) :
    ∃ e : HeightOneSpectrum (𝓞 F) → ℕ,
      (∀ v, Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e v ∧ ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e v + 1)) ∧
      Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ∧
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℝ)) ^ e v = (a : ℝ) ^ Module.finrank ℚ F := by
  set I : Ideal (𝓞 F) := Ideal.span {(a : 𝓞 F)} with hI
  have hI0 : I ≠ 0 := by
    rw [hI]; simp only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast ha.ne'
  let φ : Ideal (𝓞 F) →* ℝ :=
    ((Nat.castRingHom ℝ : ℕ →+* ℝ) : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom
  have hf := Ideal.hasFiniteMulSupport hI0
  have h1 : φ I = ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    exact map_finprod φ hf
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ ((Associates.mk v.asIdeal).count (Associates.mk I).factors) := by
    intro v; rw [HeightOneSpectrum.maxPowDividing, map_pow]; rfl
  refine ⟨fun v => (Associates.mk v.asIdeal).count (Associates.mk I).factors, fun v => ⟨?_, ?_⟩, ?_, ?_⟩
  · have h := finprod_mem_dvd v hf
    rw [Ideal.finprod_heightOneSpectrum_factorization hI0] at h
    exact Ideal.le_of_dvd h
  · intro h
    refine Ideal.finprod_not_dvd v I hI0 ?_
    rw [Ideal.finprod_heightOneSpectrum_factorization hI0]
    exact Ideal.dvd_iff_le.2 h
  · have h2 := hf.fun_comp (g := φ) (map_one φ)
    simpa only [Function.comp_def, hval] using h2
  · simp only [← hval]
    rw [← h1]
    change ((Ideal.absNorm I : ℕ) : ℝ) = _
    rw [hI, Ideal.absNorm_span_singleton]
    have h3 : (a : 𝓞 F) = algebraMap ℤ (𝓞 F) (a : ℤ) := by simp
    rw [h3, Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
    push_cast; rfl

theorem exists_den (β : F) : ∃ D : ℕ, 0 < D ∧ ∃ x : 𝓞 F, (D : F) * β = algebraMap (𝓞 F) F x := by
  have halg : IsAlgebraic ℤ β :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic β)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  let x' : 𝓞 F := ⟨y • β, hy⟩
  have hx' : algebraMap (𝓞 F) F x' = (y : F) * β := by
    change y • β = _
    rw [zsmul_eq_mul]
  rcases Int.natAbs_eq y with h1 | h1
  · refine ⟨x', ?_⟩
    rw [hx']
    conv_rhs => rw [h1]
    simp
  · refine ⟨-x', ?_⟩
    rw [map_neg, hx']
    conv_rhs => rw [h1]
    simp
end Place

section Tuples
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {d M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

def dilSet (a : ℕ) : Set (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
  {X | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}

theorem repr_natCast_mul (a : ℕ) (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr ((a : Fv F v ⊗[F] E) * y) k =
      (a : Fv F v) * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem mem_dilSet {a : ℕ} {X : Fin 1 → Fin M → Fv F v ⊗[F] E} :
    X ∈ dilSet b v a ↔ ∀ p i k, (a : Fv F v) * (Algebra.TensorProduct.basis (Fv F v) b).repr (X p i) k ∈
      v.adicCompletionIntegers F := by
  simp only [dilSet, latV, Set.mem_setOf_eq, repr_natCast_mul]

theorem dilSet_mono (a t : ℕ) : (dilSet b v a : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) ⊆ dilSet b v (a * t) := by
  intro X hX
  rw [mem_dilSet] at hX ⊢
  intro p i k
  have h := mul_mem (natCast_mem (v.adicCompletionIntegers F) t) (hX p i k)
  have e : ((a * t : ℕ) : Fv F v) * (Algebra.TensorProduct.basis (Fv F v) b).repr (X p i) k =
      (t : Fv F v) * ((a : Fv F v) * (Algebra.TensorProduct.basis (Fv F v) b).repr (X p i) k) := by
    push_cast; ring
  rw [e]; exact h

theorem exists_mem_dilSet (X : Fin 1 → Fin M → Fv F v ⊗[F] E) : ∃ n : ℕ, 0 < n ∧ X ∈ dilSet b v n := by
  choose n hn hmem using fun t : Fin 1 × Fin M × Fin d =>
    exists_nat_mul_mem v ((Algebra.TensorProduct.basis (Fv F v) b).repr (X t.1 t.2.1) t.2.2)
  refine ⟨∏ t, n t, Finset.prod_pos fun t _ => hn t, ?_⟩
  rw [mem_dilSet]
  intro p i k
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (p, i, k))
  rw [hc]
  have h := mul_mem (natCast_mem (v.adicCompletionIntegers F) c) (hmem (p, i, k))
  have e : ((n (p, i, k) * c : ℕ) : Fv F v) * (Algebra.TensorProduct.basis (Fv F v) b).repr (X p i) k =
      (c : Fv F v) * ((n (p, i, k) : Fv F v) * (Algebra.TensorProduct.basis (Fv F v) b).repr (X p i) k) := by
    push_cast; ring
  rw [e]; exact h

theorem dilSet_unit {a : ℕ} (h : (a : 𝓞 F) ∉ v.asIdeal) :
    (dilSet b v a : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) = latV b v := by
  have hv : Valued.v (a : Fv F v) = 1 := by
    have := val_eq_one v h
    simpa using this
  ext X
  rw [mem_dilSet]
  simp only [latV, Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hv, one_mul]

theorem measurable_latV : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hc : ∀ k : Fin d, Continuous fun y : Fv F v ⊗[F] E => (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
    intro k
    exact IsModuleTopology.continuous_of_linearMap
      ((Finsupp.lapply k).comp (Algebra.TensorProduct.basis (Fv F v) b).repr.toLinearMap)
  have e : (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) = ⋂ p, ⋂ i, ⋂ k,
      (fun Y : Fin 1 → Fin M → Fv F v ⊗[F] E => (Algebra.TensorProduct.basis (Fv F v) b).repr (Y p i) k) ⁻¹'
        (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext Y; simp [latV]
  rw [e]
  refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
  exact ((hc k).measurable.comp ((measurable_pi_apply i).comp (measurable_pi_apply p)))
    (Valued.isOpen_valuationSubring _).measurableSet

theorem exists_pos_mass (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (h : μ ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ μ (dilSet b v n) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [← Measure.measure_univ_eq_zero]
  have hs : (Set.univ : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) ⊆ ⋃ n : ℕ, dilSet b v (n + 1) := by
    intro X _
    obtain ⟨n, hn, hX⟩ := exists_mem_dilSet b v X
    exact Set.mem_iUnion.2 ⟨n - 1, by rwa [Nat.sub_add_cancel hn]⟩
  exact measure_mono_null hs (measure_iUnion_null fun n => hc (n + 1) n.succ_pos)
end Tuples

section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}

def mL (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (s : F) (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0∞ :=
  m v (hermScal (Fv F v) σ (algebraMap F _ s)) (latV b v)

theorem eventually_half (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 →
      1 / 2 ≤ (m v (hermScal (Fv F v) σ s) (latV b v)).toReal := by
  filter_upwards [GlobalTheory.T.rank_one_local_density_almost_all F E σ hσ M J hJ hM d b] with v hv s hs hs0
  have h := hv (lam v) (hlam v) (m v) (hm v) s hs hs0
  have hq : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_norm v
  have hpow : (4 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (M - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hq _
  have h2 : 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have := (abs_le.1 (h.trans h2)).1
  linarith

theorem scal_fin (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    {s : F} (hs : s ≠ 0) :
    (∀ v, mL σ b m s v < ⊤) ∧ Summable fun v => |(mL σ b m s v).toReal - 1| := by
  let T : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E s
  have hT : ∀ a c, σ (T c a) = T a c := by intro a c; simp [T]
  have hdet : T.det ≠ 0 := by
    rw [Matrix.det_unique]
    exact (map_ne_zero (algebraMap F E)).2 hs
  obtain ⟨s', hs', -, hh⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hσ T hT
  have e : s' = s := by
    have := congrFun (congrFun hs' 0) 0
    exact ((algebraMap F E).injective this).symm
  subst e
  have h := GlobalTheory.T.hermitian_rank_one_local_volume F E σ hσ M J hJ 1 rfl (by omega) T hT hdet d b lam hlam m hm
  simp only [hh] at h
  exact h

theorem dil_eq (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    (v : HeightOneSpectrum (𝓞 F)) (t : F) (a e : ℕ) (ha : 0 < a)
    (h1 : Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e) (h2 : ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1)) :
    m v (hermScal (Fv F v) σ (algebraMap F _ t)) (dilSet b v a) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (e * (2 * M - 2)) * mL σ b m ((a : F) ^ 2 * t) v := by
  have h := GlobalTheory.T.local_rank_one_density_uniformizer_power F E σ hσ M J hJ d b v (lam v) (hlam v) (m v) (hm v) (by omega) a e ha h1 h2
    (algebraMap F _ t) (latV b v) (measurable_latV b v)
  rw [show ((a : Fv F v) ^ 2 * algebraMap F _ t) = algebraMap F _ ((a : F) ^ 2 * t) by simp] at h
  exact h

theorem growth_main (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    (β : F) (hβ : β ≠ 0) (hne : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧ c * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤
      ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v a)).toReal := by
  classical
  have hgood := eventually_half (b := b) hσ hJ hM hlam hm
  have hB := Filter.eventually_cofinite.1 hgood
  set B := hB.toFinset with hBdef
  have hBg : ∀ v, v ∉ B → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 →
      1 / 2 ≤ (m v (hermScal (Fv F v) σ s) (latV b v)).toReal := by
    intro v hv
    simpa [B] using hv
  choose nv hnv0 hnv using fun v => exists_pos_mass b v _ (hne v)
  obtain ⟨D₀, hD₀, x, hx⟩ := exists_den β
  set N := D₀ * ∏ v ∈ B, nv v with hNdef
  have hN : 0 < N := Nat.mul_pos hD₀ (Finset.prod_pos fun v _ => hnv0 v)
  set Q := ∏ v ∈ B, Ideal.absNorm v.asIdeal with hQdef
  have hQ : 0 < Q := Finset.prod_pos fun v _ => by have := two_le_norm v; omega
  set p := Q + 1 with hpdef
  have hp2 : 2 ≤ p := by omega
  have hpB : ∀ v ∈ B, (p : 𝓞 F) ∉ v.asIdeal := by
    intro v hv hmem
    have hQm : (Q : 𝓞 F) ∈ v.asIdeal := by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal) hv
      rw [hQdef, hc]; push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem hmem hQm
      simpa [hpdef] using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hp0 : (p : 𝓞 F) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hP : {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 F)}) ?_).subset ?_
    · simpa using hp0
    · intro v hv
      exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  set P := hP.toFinset with hPdef
  have hPmem : ∀ v, v ∈ P ↔ (p : 𝓞 F) ∈ v.asIdeal := by intro v; simp [P]
  have hβF : ∀ n : ℕ, 0 < n → (n : F) ^ 2 * β ≠ 0 := fun n hn =>
    mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn.ne')) hβ
  have hint : ∀ n : ℕ, D₀ ∣ n → ∀ v, algebraMap F (Fv F v) ((n : F) ^ 2 * β) ∈ v.adicCompletionIntegers F := by
    rintro n ⟨c, rfl⟩ v
    have e : (((D₀ * c : ℕ) : F)) ^ 2 * β = algebraMap (𝓞 F) F (((D₀ * c ^ 2 : ℕ) : 𝓞 F) * x) := by
      rw [map_mul, ← hx, map_natCast]; push_cast; ring
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact val_le_one v _
  have hfin := fun n (hn : 0 < n) => scal_fin (b := b) hσ hJ hM hlam hm (hβF n hn)
  have hhalf : ∀ n : ℕ, 0 < n → D₀ ∣ n → ∀ v, v ∉ B → 1 / 2 ≤ (mL σ b m ((n : F) ^ 2 * β) v).toReal := by
    intro n hn hd v hv
    exact hBg v hv _ (hint n hd v) ((map_ne_zero _).2 (hβF n hn))
  have hDN : D₀ ∣ N := Dvd.intro _ rfl
  have hupos : ∀ v, 0 < (mL σ b m ((N : F) ^ 2 * β) v).toReal := by
    intro v
    by_cases hv : v ∈ B
    · obtain ⟨e, he, -, -⟩ := exists_exponents (F := F) N hN
      have h := dil_eq (b := b) hσ hJ hM hlam hm v β N (e v) hN (he v).1 (he v).2
      have hnz : m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v N) ≠ 0 := by
        obtain ⟨c, hc⟩ : nv v ∣ N := (Finset.dvd_prod_of_mem nv hv).mul_left _
        intro h0
        refine hnv v (measure_mono_null ?_ h0)
        rw [hc]; exact dilSet_mono b v _ _
      have hz : mL σ b m ((N : F) ^ 2 * β) v ≠ 0 := by
        intro h0
        rw [h, h0, mul_zero] at hnz
        exact hnz rfl
      exact ENNReal.toReal_pos hz ((hfin N hN).1 v).ne
    · have := hhalf N hN hDN v hv
      linarith
  have hcop : ∀ v, (p : 𝓞 F) ∉ v.asIdeal → ∀ k : ℕ,
      mL σ b m (((N * p ^ k : ℕ) : F) ^ 2 * β) v = mL σ b m ((N : F) ^ 2 * β) v := by
    intro v hv k
    have hpk : ((p ^ k : ℕ) : 𝓞 F) ∉ v.asIdeal := by
      push_cast
      exact fun h => hv (v.isPrime.mem_of_pow_mem _ h)
    have h := dil_eq (b := b) hσ hJ hM hlam hm v ((N : F) ^ 2 * β) (p ^ k) 0 (by positivity) (by simp)
      (by simpa using fun h' => hpk ((Ideal.span_singleton_le_iff_mem _).1 h'))
    rw [dilSet_unit b v hpk] at h
    simp only [zero_mul, pow_zero, one_mul] at h
    have e : (((N * p ^ k : ℕ) : F)) ^ 2 * β = ((p ^ k : ℕ) : F) ^ 2 * ((N : F) ^ 2 * β) := by
      push_cast; ring
    rw [e]
    exact h.symm
  have hsub : Summable fun v : {v // v ∉ P} => |(mL σ b m ((N : F) ^ 2 * β) v.1).toReal - 1| :=
    (hfin N hN).2.comp_injective Subtype.val_injective
  have hC := (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ P} (fun v => (mL σ b m ((N : F) ^ 2 * β) v.1).toReal) hsub).2.2.1
    fun v => hupos v.1
  set C := ∏' v : {v // v ∉ P}, (mL σ b m ((N : F) ^ 2 * β) v.1).toReal with hCdef
  refine ⟨(1 / 2) ^ P.card * C, by positivity, fun k => ⟨N * p ^ k, ?_, ?_⟩⟩
  · calc k < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ p ^ k := Nat.pow_le_pow_left hp2 k
      _ ≤ N * p ^ k := Nat.le_mul_of_pos_left _ hN
  set a := N * p ^ k with hadef
  have ha : 0 < a := by positivity
  have hDa : D₀ ∣ a := hDN.mul_right _
  have hw := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ (fun v => (mL σ b m ((a : F) ^ 2 * β) v).toReal) (hfin a ha).2
  obtain ⟨e, he, hfs, hprod⟩ := exists_exponents (F := F) a ha
  have hid : ∀ v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v a)).toReal =
      (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2) * (mL σ b m ((a : F) ^ 2 * β) v).toReal := by
    intro v
    rw [dil_eq (b := b) hσ hJ hM hlam hm v β a (e v) ha (he v).1 (he v).2, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, pow_mul]
  have hf2 : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    hfs.fun_comp (g := fun y : ℝ => y ^ (2 * M - 2)) (one_pow _)
  have hmul : Multipliable
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    (hasProd_prod_of_ne_finset_one (s := Set.Finite.toFinset hf2) (fun v hv =>
      by_contra fun h => hv ((Set.Finite.mem_toFinset hf2).2 h))).multipliable
  rw [tprod_congr hid, hmul.tprod_mul hw.1, tprod_eq_finprod hf2, ← finprod_pow hfs, hprod, ← pow_mul]
  have hlow : (1 / 2 : ℝ) ^ P.card * C ≤ ∏' v, (mL σ b m ((a : F) ^ 2 * β) v).toReal := by
    rw [(hw.2.1 P).2]
    have e2 : ∏' v : {v // v ∉ P}, (mL σ b m ((a : F) ^ 2 * β) v.1).toReal = C :=
      tprod_congr fun v => by rw [hadef, hcop v.1 (fun h => v.2 ((hPmem _).2 h)) k]
    rw [e2]
    refine mul_le_mul_of_nonneg_right ?_ hC.le
    calc (1 / 2 : ℝ) ^ P.card = ∏ _v ∈ P, (1 / 2 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) fun v hv =>
        hhalf a ha hDa v fun hvB => hpB v hvB ((hPmem v).1 hv)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hlow (by positivity)

end Main

theorem growth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ β : F, β ≠ 0 → (∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0) → ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧ c * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b lam hlam m hm β hβ hne
  exact growth_main hσ hJ hM hlam hm β hβ hne

end GlobalTheory.CompanionTheory.SW.Growth
